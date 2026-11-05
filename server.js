'use strict';
// せーの指名 サーバー。Node.js 18以上、外部パッケージなし。
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const DATA_FILE = path.join(process.env.DATA_DIR || __dirname, 'data.json');
const INDEX = path.join(__dirname, 'public', 'index.html');
const ROOM_TTL_MS = 72 * 3600 * 1000; // 最後の操作から72時間で部屋を自動削除
const MAX_MEMBERS = 200;
const GENDERS = ['male', 'female'];

// ---------- 永続化 ----------
let rooms = {};
try { rooms = JSON.parse(fs.readFileSync(DATA_FILE, 'utf8')); } catch (e) { rooms = {}; }
// 以前の版で作られた部屋には、モードとチーム名がないので既定値を補う
for (const r of Object.values(rooms)) { r.mode = r.mode || 'double'; r.teams = r.teams || ['男性', '女性']; }
let saveTimer = null;
function save() {
  if (saveTimer) return;
  saveTimer = setTimeout(() => {
    saveTimer = null;
    fs.writeFile(DATA_FILE + '.tmp', JSON.stringify(rooms), (err) => {
      if (!err) fs.rename(DATA_FILE + '.tmp', DATA_FILE, () => {});
    });
  }, 300);
}
setInterval(() => {
  const now = Date.now();
  let changed = false;
  for (const id of Object.keys(rooms)) {
    if (now - rooms[id].lastActive > ROOM_TTL_MS) { delete rooms[id]; changed = true; }
  }
  if (changed) save();
}, 3600 * 1000).unref();

// ---------- 小道具 ----------
class HttpError extends Error { constructor(status, msg) { super(msg); this.status = status; } }
const fail = (status, msg) => { throw new HttpError(status, msg); };
const rand = (n) => crypto.randomBytes(n).toString('hex');
const hashPw = (pw, salt) => crypto.scryptSync(String(pw), salt, 32).toString('hex');
function safeEq(a, b) {
  const A = Buffer.from(String(a)), B = Buffer.from(String(b));
  return A.length === B.length && crypto.timingSafeEqual(A, B);
}
const normName = (s) => String(s || '').normalize('NFKC').trim().replace(/\s+/g, ' ');

// 簡易レート制限
const buckets = new Map();
function bucket(key, windowMs) {
  const now = Date.now();
  let b = buckets.get(key);
  if (!b || b.reset < now) { b = { n: 0, reset: now + windowMs }; buckets.set(key, b); }
  return b;
}
const isBlocked = (key, max, windowMs) => bucket(key, windowMs).n >= max;
const addHit = (key, windowMs) => { bucket(key, windowMs).n++; };
setInterval(() => { const now = Date.now(); for (const [k, b] of buckets) if (b.reset < now) buckets.delete(k); }, 600 * 1000).unref();

function clientIp(req) {
  const xf = req.headers['x-forwarded-for'];
  return (xf ? String(xf).split(',')[0].trim() : req.socket.remoteAddress) || 'unknown';
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    let size = 0; const chunks = [];
    req.on('data', (c) => {
      size += c.length;
      if (size > 20000) { reject(new HttpError(413, '送信内容が大きすぎます')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => {
      if (!chunks.length) return resolve({});
      try { resolve(JSON.parse(Buffer.concat(chunks).toString('utf8'))); }
      catch (e) { reject(new HttpError(400, '不正なリクエストです')); }
    });
    req.on('error', reject);
  });
}

function send(res, status, obj) {
  const body = JSON.stringify(obj);
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'cache-control': 'no-store',
    'x-content-type-options': 'nosniff',
  });
  res.end(body);
}

// ---------- ドメインロジック ----------
const memberById = (room, id) => room.members.find((m) => m.id === id);
const activeMembers = (room) => room.members.filter((m) => !m.partnerId);

function computeResult(room, round) {
  const act = activeMembers(room);
  const picks = room.picks[round] || {};
  const incoming = {};
  act.forEach((m) => { incoming[m.id] = []; });
  for (const m of act) {
    const t = picks[m.id];
    if (t && incoming[t]) incoming[t].push(m.id);
  }
  // 内部の maleId / femaleId は「1人目 / 2人目」の意味。ダブルモードでは チーム1 / チーム2、
  // シングルモードでは名簿の並びで先に出てきた方が1人目になる
  const matches = [];
  const matched = new Set();
  for (const m of act) {
    if (matched.has(m.id)) continue;
    const t = picks[m.id];
    if (t && incoming[t] && picks[t] === m.id) {
      const [a, b] = (room.mode === 'double' && m.gender !== 'male') ? [t, m.id] : [m.id, t];
      matches.push({
        maleId: a,
        femaleId: b,
        maleOthers: incoming[a].filter((x) => x !== b),
        femaleOthers: incoming[b].filter((x) => x !== a),
      });
      matched.add(a); matched.add(b);
    }
  }
  const unmatched = act.filter((m) => !matched.has(m.id)).map((m) => ({
    id: m.id, picked: picks[m.id] || null, received: incoming[m.id],
  }));
  return { round, matches, unmatched };
}

function hasNextRound(room) {
  const a = activeMembers(room);
  if (room.mode === 'single') return a.length >= 2;
  return a.some((m) => m.gender === 'male') && a.some((m) => m.gender === 'female');
}

// 指名できる相手か(ダブル: 相手チームの未成立者 / シングル: 自分以外の未成立者)
function canPick(room, me, t) {
  if (t.id === me.id || t.partnerId) return false;
  return room.mode === 'single' || t.gender !== me.gender;
}

function roomInfo(room, hideActive) {
  const m = room.members, a = activeMembers(room);
  const info = {
    id: room.id, name: room.name, phase: room.phase, round: room.round,
    mode: room.mode, teams: room.teams,
    counts: { total: m.length, male: m.filter((x) => x.gender === 'male').length, female: m.filter((x) => x.gender === 'female').length },
  };
  if (!hideActive) {
    info.counts.activeTotal = a.length;
    info.counts.activeMale = a.filter((x) => x.gender === 'male').length;
    info.counts.activeFemale = a.filter((x) => x.gender === 'female').length;
  }
  return info;
}

function nameOf(room, id) { const m = memberById(room, id); return m ? m.name : '?'; }

// すれ違い: 今回 x が y を指名したが、y は x を指名しておらず(成立していない)、
// y は以前の周で x を指名していた、という組を集める
function crossingsFor(room, round) {
  const cur = room.picks[round] || {};
  const out = [];
  for (const [x, y] of Object.entries(cur)) {
    if (cur[y] === x) continue;
    const rounds = [];
    for (let r = 1; r < round; r++) if ((room.picks[r] || {})[y] === x) rounds.push(r);
    if (rounds.length) {
      out.push({ now: nameOf(room, x), before: nameOf(room, y), rounds, beforeNow: cur[y] ? nameOf(room, cur[y]) : null });
    }
  }
  return out;
}

// 成立した2人の間で、以前の周にあった指名
function pairHistory(room, round, aId, bId) {
  const out = [];
  for (let r = 1; r < round; r++) {
    const p = room.picks[r] || {};
    if (p[aId] === bId) out.push({ round: r, from: nameOf(room, aId), to: nameOf(room, bId) });
    if (p[bId] === aId) out.push({ round: r, from: nameOf(room, bId), to: nameOf(room, aId) });
  }
  return out;
}

function resolveResult(room, r) {
  const ref = (id) => ({ id, name: nameOf(room, id) });
  return {
    round: r.round,
    crossings: crossingsFor(room, r.round),
    matches: r.matches.map((x) => ({
      male: ref(x.maleId), female: ref(x.femaleId),
      maleOthers: x.maleOthers.length, femaleOthers: x.femaleOthers.length,
      history: pairHistory(room, r.round, x.maleId, x.femaleId),
    })),
    unmatched: r.unmatched.map((u) => {
      const m = memberById(room, u.id);
      return { id: u.id, name: m.name, gender: m.gender, picked: u.picked ? nameOf(room, u.picked) : null, received: u.received.length };
    }),
    picks: Object.entries(room.picks[r.round] || {}).map(([from, to]) => ({ from: nameOf(room, from), to: nameOf(room, to) })),
  };
}

function couplesOf(room, uptoRound) {
  const out = [];
  for (const r of room.results) {
    if (r.round > uptoRound) continue;
    for (const x of r.matches) out.push({ round: r.round, male: nameOf(room, x.maleId), female: nameOf(room, x.femaleId) });
  }
  return out;
}

function hostView(room) {
  const picks = room.picks[room.round] || {};
  const members = room.members.map((m) => ({
    id: m.id, name: m.name, gender: m.gender,
    partner: m.partnerId ? nameOf(room, m.partnerId) : null,
    picked: room.phase === 'picking' && !m.partnerId ? !!picks[m.id] : null,
  }));
  const shown = ['reveal', 'between', 'done'].includes(room.phase);
  const cur = shown ? room.results.find((r) => r.round === room.round) : null;
  return {
    role: 'host',
    room: roomInfo(room),
    members,
    result: cur ? resolveResult(room, cur) : null,
    couples: couplesOf(room, room.round),
    canStart: hasNextRound(room),
  };
}

function memberView(room, me) {
  const reveal = room.phase === 'reveal';
  const picks = room.picks[room.round] || {};
  const iAmActive = !me.partnerId || reveal;
  let candidates = null;
  if (room.phase === 'picking' && !me.partnerId) {
    candidates = room.members
      .filter((m) => canPick(room, me, m))
      .map((m) => ({ id: m.id, name: m.name }));
  }
  const settled = room.phase === 'between' || room.phase === 'done';
  return {
    role: 'member',
    room: roomInfo(room, reveal),
    me: {
      id: me.id, name: me.name, gender: me.gender,
      active: iAmActive,
      partner: !reveal && me.partnerId ? nameOf(room, me.partnerId) : null,
      matchedThisRound: !reveal && me.matchedRound === room.round,
    },
    candidates,
    myPick: room.phase === 'picking' ? picks[me.id] || null : null,
    couples: settled ? couplesOf(room, room.round) : [],
  };
}

function authRoom(req, room) {
  const token = String(req.headers['x-token'] || '');
  if (!token) fail(401, 'ログインが必要です');
  if (room.hostToken && safeEq(token, room.hostToken)) return { host: true };
  const me = room.members.find((m) => safeEq(token, m.token));
  if (me) return { member: me };
  fail(401, 'ログインが切れました。入り直してください');
}
const needHost = (a) => { if (!a.host) fail(403, '部屋主のみ実行できます'); };

// ---------- ルーティング ----------
async function handleApi(req, res, p) {
  const parts = p.split('/').filter(Boolean); // ['api','rooms',id,action,...]
  const ip = clientIp(req);
  if (parts[1] !== 'rooms') fail(404, 'not found');

  // 部屋一覧・作成
  if (parts.length === 2) {
    if (req.method === 'GET') {
      const list = Object.values(rooms)
        .sort((a, b) => b.createdAt - a.createdAt)
        .map((r) => ({ id: r.id, name: r.name, phase: r.phase, round: r.round, count: r.members.length, mode: r.mode }));
      return send(res, 200, { rooms: list });
    }
    if (req.method === 'POST') {
      if (isBlocked('create|' + ip, 20, 3600 * 1000)) fail(429, '部屋を作りすぎです。しばらくしてからお試しください');
      const b = await readBody(req);
      const name = normName(b.name);
      const pw = String(b.password || '');
      if (!name || name.length > 40) fail(400, '部屋の名前は1〜40文字で入力してください');
      if (pw.length < 4 || pw.length > 64) fail(400, 'パスワードは4〜64文字にしてください');
      const mode = b.mode === 'single' ? 'single' : 'double';
      let teams = ['男性', '女性'];
      if (mode === 'double') {
        const t = Array.isArray(b.teams) ? b.teams : teams;
        teams = [normName(t[0]), normName(t[1])];
        if (!teams[0] || !teams[1] || teams[0].length > 10 || teams[1].length > 10) fail(400, 'チーム名は、2つとも1〜10文字で入力してください');
        if (teams[0].toLowerCase() === teams[1].toLowerCase()) fail(400, '2つのチーム名は、別の名前にしてください');
      }
      if (Object.keys(rooms).length >= 9000) fail(503, '部屋が満杯です');
      let id;
      do { id = String(Math.floor(1000 + Math.random() * 9000)); } while (rooms[id]);
      const salt = rand(16);
      const hostToken = rand(24);
      const hostKey = crypto.randomBytes(5).toString('hex').toUpperCase();
      rooms[id] = {
        id, name, mode, teams, salt, pwHash: hashPw(pw, salt), hostKeyHash: hashPw(hostKey, salt), hostToken,
        phase: 'lobby', round: 0, members: [], picks: {}, results: [],
        createdAt: Date.now(), lastActive: Date.now(),
      };
      addHit('create|' + ip, 3600 * 1000);
      save();
      return send(res, 200, { id, hostToken, hostKey });
    }
    fail(405, 'method not allowed');
  }

  const room = rooms[parts[2]];
  if (!room) fail(404, '部屋が見つかりません');
  const action = parts[3] || '';

  if (req.method === 'GET' && action === 'public') {
    return send(res, 200, { id: room.id, name: room.name, phase: room.phase, round: room.round, count: room.members.length, mode: room.mode, teams: room.teams });
  }

  // 参加(部屋番号+パスワード)
  if (req.method === 'POST' && action === 'join') {
    const key = 'join|' + ip + '|' + room.id;
    if (isBlocked(key, 8, 600 * 1000)) fail(429, 'パスワードを間違えすぎです。10分後にもう一度お試しください');
    const b = await readBody(req);
    if (!safeEq(hashPw(b.password || '', room.salt), room.pwHash)) { addHit(key, 600 * 1000); fail(403, 'パスワードが違います'); }
    const name = normName(b.name);
    if (!name || name.length > 20) fail(400, 'お名前は1〜20文字で入力してください');
    const existing = room.members.find((m) => m.name.toLowerCase() === name.toLowerCase());
    if (existing) {
      // 同じ名前で入り直すと、性別の入力なしで元の参加者に戻り、直前の画面が表示される
      existing.token = rand(24);
      room.lastActive = Date.now(); save();
      return send(res, 200, { token: existing.token, memberId: existing.id, rejoined: true });
    }
    if (room.phase !== 'lobby') fail(409, 'この名前の参加者が見つかりません。登録した名前と同じか確認してください(ひらがな・カタカナの違いなど)。開始後は新しく参加できません');
    const single = room.mode === 'single';
    if (!single && !GENDERS.includes(b.gender)) fail(400, '自分が入るチームを選んでください');
    if (room.members.length >= MAX_MEMBERS) fail(409, '定員に達しました');
    const m = { id: rand(6), token: rand(24), name, gender: single ? 'single' : b.gender, partnerId: null, matchedRound: null, joinedAt: Date.now() };
    room.members.push(m);
    room.lastActive = Date.now(); save();
    return send(res, 200, { token: m.token, memberId: m.id });
  }

  // 部屋主の復帰
  if (req.method === 'POST' && action === 'host-login') {
    const key = 'host|' + ip + '|' + room.id;
    if (isBlocked(key, 8, 600 * 1000)) fail(429, '間違えすぎです。10分後にもう一度お試しください');
    const b = await readBody(req);
    if (!safeEq(hashPw(String(b.hostKey || '').trim().toUpperCase(), room.salt), room.hostKeyHash)) {
      addHit(key, 600 * 1000); fail(403, '復帰コードが違います');
    }
    room.hostToken = rand(24); save();
    return send(res, 200, { token: room.hostToken });
  }

  const auth = authRoom(req, room);
  room.lastActive = Date.now();

  if (req.method === 'GET' && action === 'state') {
    return send(res, 200, auth.host ? hostView(room) : memberView(room, auth.member));
  }

  if (req.method === 'POST' && action === 'pick') {
    if (!auth.member) fail(403, '参加者のみ実行できます');
    if (room.phase !== 'picking') fail(409, '今は選べません');
    const me = auth.member;
    if (me.partnerId) fail(409, 'あなたはすでにカップル成立済みです');
    const b = await readBody(req);
    const t = memberById(room, b.targetId);
    if (!t || !canPick(room, me, t)) fail(400, 'その人は選べません');
    room.picks[room.round][me.id] = t.id;
    save();
    return send(res, 200, { ok: true });
  }

  // ここから部屋主のみ
  if (req.method === 'POST' && action === 'host') {
    needHost(auth);
    const op = parts[4];
    if (op === 'start') {
      if (!['lobby', 'between'].includes(room.phase)) fail(409, '今は開始できません');
      if (!hasNextRound(room)) fail(409, '男性と女性がそれぞれ1人以上必要です');
      room.round += 1;
      room.picks[room.round] = {};
      room.phase = 'picking';
    } else if (op === 'close') {
      if (room.phase !== 'picking') fail(409, '今は締め切れません');
      const r = computeResult(room, room.round);
      room.results.push(r);
      for (const x of r.matches) {
        const a = memberById(room, x.maleId), b = memberById(room, x.femaleId);
        a.partnerId = b.id; b.partnerId = a.id; a.matchedRound = b.matchedRound = room.round;
      }
      room.phase = 'reveal';
    } else if (op === 'finish') {
      if (room.phase !== 'reveal') fail(409, '今は終了できません');
      room.phase = hasNextRound(room) ? 'between' : 'done';
    } else if (op === 'end') {
      if (!['lobby', 'between'].includes(room.phase)) fail(409, '今は終了できません');
      room.phase = 'done';
    } else if (op === 'remove') {
      if (room.phase !== 'lobby') fail(409, '開始前のみ削除できます');
      const b = await readBody(req);
      room.members = room.members.filter((m) => m.id !== b.memberId);
    } else if (op === 'delete') {
      delete rooms[room.id];
    } else fail(404, 'not found');
    save();
    return send(res, 200, { ok: true });
  }

  fail(404, 'not found');
}

const server = http.createServer(async (req, res) => {
  try {
    const p = new URL(req.url, 'http://localhost').pathname;
    if (req.method === 'GET' && (p === '/' || p === '/index.html')) {
      const html = fs.readFileSync(INDEX);
      res.writeHead(200, {
        'content-type': 'text/html; charset=utf-8',
        'cache-control': 'no-cache',
        'x-content-type-options': 'nosniff',
        'content-security-policy': "default-src 'self'; style-src 'unsafe-inline'; script-src 'unsafe-inline'; frame-ancestors 'none'",
      });
      return res.end(html);
    }
    if (p.startsWith('/api/')) return await handleApi(req, res, p);
    send(res, 404, { error: 'not found' });
  } catch (e) {
    if (e instanceof HttpError) return send(res, e.status, { error: e.message });
    console.error(e);
    send(res, 500, { error: 'サーバーでエラーが起きました' });
  }
});

server.listen(PORT, () => console.log('せーの指名: http://localhost:' + PORT));
