#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Танковая битва 3D — сетевой сервер (кооп: игроки + волны ИИ).

Чистый asyncio, свой минимальный WebSocket (RFC 6455), без внешних зависимостей.
Запуск:  python3 server.py [port]   (по умолчанию 8765)
Клиент:  открыть tanks3d.html на том же хосте и нажать «СЕТЕВОЙ БОЙ».
"""
import asyncio, base64, hashlib, json, math, random, struct, sys, time

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8765
DEG = math.pi / 180.0
TANK_R = 26
SHELL_SPEED = 720
ARENA_W, ARENA_H = 3000, 2000
VIEW = 650
PREF_DIST = {'light': 280, 'medium': 330, 'heavy': 300, 'td': 560}
PEN = {'light': 40, 'medium': 55, 'heavy': 75, 'td': 100}
PER = {'light': 4, 'medium': 5, 'heavy': 6, 'td': 7}
ARMOR = {
    'light': (45, 30, 22), 'medium': (90, 60, 45),
    'heavy': (175, 110, 82), 'td': (100, 65, 50)
}
VEH = json.load(open('vehicles.json', encoding='utf-8'))

# ---------------- утилиты ----------------
def angNorm(a):
    while a > math.pi: a -= 2 * math.pi
    while a < -math.pi: a += 2 * math.pi
    return a

def clamp(v, lo, hi): return lo if v < lo else hi if v > hi else v

def rotateToward(cur, target, maxDelta):
    d = angNorm(target - cur)
    if abs(d) <= maxDelta: return target
    return cur + (1 if d > 0 else -1) * maxDelta

def circleRectHit(cx, cz, r, x, y, w, h):
    nx = clamp(cx, x, x + w); nz = clamp(cz, y, y + h)
    dx = cx - nx; dz = cz - nz
    return dx * dx + dz * dz < r * r

def vehPen(v):
    return round(PEN[v['type']] + v['tier'] * PER[v['type']])

def zoneOf(bx, bz, t):
    brg = angNorm(math.atan2(bz - t['z'], bx - t['x']) - t['a'])
    if abs(brg) < 0.6: return 0            # front
    if abs(brg) > 2.5: return 2            # rear
    return 1                               # side

# ---------------- мир (ровная земля, без холмов) ----------------
RAND = random.Random(20240601)
def heightAt(x, z):
    return 0.0

walls = []   # {x,y,w,h,crate|None}
def genWalls():
    global walls
    walls = []
    t = 40
    walls.append({'x': -t, 'y': -t, 'w': ARENA_W + 2 * t, 'h': t})
    walls.append({'x': -t, 'y': ARENA_H, 'w': ARENA_W + 2 * t, 'h': t})
    walls.append({'x': -t, 'y': 0, 'w': t, 'h': ARENA_H})
    walls.append({'x': ARENA_W, 'y': 0, 'w': t, 'h': ARENA_H})
    for _ in range(14):
        w = RAND.uniform(140, 340); h = RAND.uniform(100, 260)
        x = RAND.uniform(120, ARENA_W - 120 - w); y = RAND.uniform(120, ARENA_H - 120 - h)
        if (x + w > ARENA_W / 2 - 200 and x < ARENA_W / 2 + 200 and
                y + h > ARENA_H / 2 - 200 and y < ARENA_H / 2 + 200):
            continue
        walls.append({'x': x, 'y': y, 'w': w, 'h': h})
    for _ in range(10):
        s = 52
        x = RAND.uniform(140, ARENA_W - 140 - s); y = RAND.uniform(140, ARENA_H - 140 - s)
        if (x + s > ARENA_W / 2 - 150 and x < ARENA_W / 2 + 150 and
                y + s > ARENA_H / 2 - 150 and y < ARENA_H / 2 + 150):
            continue
        walls.append({'x': x, 'y': y, 'w': s, 'h': s, 'crate': True})

def wallBlocking(x, z, r):
    for w in walls:
        if circleRectHit(x, z, r, w['x'], w['y'], w['w'], w['h']): return w
    return None

def resolveTankWalls(t):
    for w in walls:
        nx = clamp(t['x'], w['x'], w['x'] + w['w']); nz = clamp(t['z'], w['y'], w['y'] + w['h'])
        dx = t['x'] - nx; dz = t['z'] - nz
        d2 = dx * dx + dz * dz
        if d2 < TANK_R * TANK_R:
            d = math.sqrt(d2) or 0.001
            push = (TANK_R - d) / d
            t['x'] += dx * push; t['z'] += dz * push
    t['x'] = clamp(t['x'], TANK_R, ARENA_W - TANK_R)
    t['z'] = clamp(t['z'], TANK_R, ARENA_H - TANK_R)

def resolvePairs():
    for i in range(len(units)):
        for j in range(i + 1, len(units)):
            a = units[i]; b = units[j]
            if not a['al'] or not b['al']: continue
            d = math.hypot(b['x'] - a['x'], b['z'] - a['z'])
            if d < TANK_R * 2 and d > 0.001:
                push = (TANK_R * 2 - d) / 2 / d
                a['x'] -= (b['x'] - a['x']) * push; a['z'] -= (b['z'] - a['z']) * push
                b['x'] += (b['x'] - a['x']) * push; b['z'] += (b['z'] - a['z']) * push

# ---------------- состояние мира ----------------
units = []       # игроки и враги: dict
bullets = []     # снаряды
sseq = 0         # sequence
players = {}     # ws -> unit (игрок)
wave = 0
waveTimer = 1.2
bid = 0          # счётчик id снарядов

# дуэль 1×1 (как в WoT)
worldMode = 'coop'    # 'coop' | 'duel'
duelScore = {}        # id игрока -> число побед в раундах
duelRound = 1
duelWinner = None     # id победителя матча (до 5 побед)
duelEndT = 0          # таймер сброса после конца матча

def duelSpawn(side):
    """Спавн на своей половине: side 0 — лево, 1 — право."""
    zc = ARENA_H / 2
    if side == 0:
        for x in range(600, 1200, 60):
            if not wallBlocking(x, zc, TANK_R + 4): return x, zc, 0.0
        return 600, zc, 0.0
    for x in range(ARENA_W - 600, ARENA_W - 1200, -60):
        if not wallBlocking(x, zc, TANK_R + 4): return x, zc, math.pi
    return ARENA_W - 600, zc, math.pi

def newUnit(vehId, team, x, z, a=None, st=None):
    v = VEH[vehId]
    t = {
        'id': '', 'veh': vehId, 'v': v, 'team': team, 'x': x, 'z': z,
        'a': a if a is not None else RAND.uniform(0, 6.28),
        'tu': a if a is not None else 0, 'el': 0.02,
        'sp': v['speed'], 'hp': v['hp'], 'mh': v['hp'],
        'dmg': v['dmg'] * (st['dmg'] if st else 1),
        'cd': max(0.6, v['cd']) * (st['cd'] if st else 1),
        'al': True,
        'fireT': 0, 'recoil': 0,
        'pen': vehPen(v), 'armor': ARMOR[v['type']],
        'clipSize': int(v.get('clip') or (v.get('cycleSize') if v.get('cycle') else 0)),
        'clipLeft': 0, 'magState': 'ready', 'cycleAcc': 0,
        'wi': 0,  # wheelVel визуал
        'ai': None if team == 'player' else {'t': 0, 'strafeDir': 1, 'aimErr': 0.4, 'weaveT': 0, 'weave': 0, 'stuckT': 0, 'evadeT': 0}
    }
    t['clipLeft'] = t['clipSize']
    return t

def unitSpeed(t):
    return t['sp']

def updateMagT(t, dt):
    t['fireT'] -= dt
    if not t['clipSize']: return
    if t['magState'] == 'reloading':
        if t['fireT'] <= 0:
            t['magState'] = 'ready'; t['clipLeft'] = t['clipSize']; t['fireT'] = 0
    elif t['v'].get('cycle') and t['clipLeft'] < t['clipSize']:
        t['cycleAcc'] += dt
        if t['cycleAcc'] >= t['v'].get('cycleStep', 1):
            t['cycleAcc'] = 0; t['clipLeft'] += 1

def canFireT(t):
    return t['fireT'] <= 0 and (not t['clipSize'] or (t['magState'] == 'ready' and t['clipLeft'] > 0))

def fireDirect(t, el):
    global bid
    v = t['v']
    ln = (v.get('barrelLen') or 46) * (v.get('scale') or 1) * 0.9 + 6
    bx = t['x'] + math.cos(t['tu']) * ln
    bz = t['z'] + math.sin(t['tu']) * ln
    by = heightAt(t['x'], t['z']) + 31
    bid += 1
    bullets.append({
        'id': 'b%d' % bid, 'x': bx, 'y': by, 'z': bz, 'team': t['team'], 'from': t['id'],
        'dmg': t['dmg'], 'pen': t['pen'], 'life': 2.2,
        'vx': math.cos(t['tu']) * math.cos(el) * SHELL_SPEED,
        'vy': math.sin(el) * SHELL_SPEED,
        'vz': math.sin(t['tu']) * math.cos(el) * SHELL_SPEED
    })
    fx({'k': 'fire', 'i': t['id'], 'x': bx, 'y': by, 'z': bz})
    t['recoil'] = 1
    if t['team'] == 'enemy': t['rev'] = True
    if t['clipSize']:
        t['clipLeft'] -= 1
        if t['clipLeft'] <= 0 and not t['v'].get('cycle'):
            t['magState'] = 'reloading'; t['fireT'] = t['v'].get('clipReload') or 3
        else:
            t['magState'] = 'ready'; t['fireT'] = t['v'].get('between') or 0.8; t['cycleAcc'] = 0
    else:
        t['fireT'] = t['cd']

def damage(t, dmg, atX, atY, atZ, team):
    global duelScore, duelRound, duelWinner, duelEndT
    if not t['al']: return
    t['hp'] -= dmg
    if t['hp'] <= 0:
        t['al'] = False
        fx({'k': 'boom', 'x': t['x'], 'z': t['z']})
        if t['team'] == 'enemy':
            money = 80 + wave * 10
            fx({'k': 'kill', 'v': t['id'], 'by': team, 'money': money})
        else:
            fx({'k': 'dead', 'i': t['id']})
            t['respawnT'] = 3.0 if worldMode == 'duel' else 4.0
            if worldMode == 'duel':
                alive = [u for u in units if u['team'] == 'player' and u['al'] and u is not t]
                if alive:
                    w = alive[0]['id']
                    duelScore[w] = duelScore.get(w, 0) + 1
                    fx({'k': 'rwin', 'winner': w, 'score': dict(duelScore), 'round': duelRound})
                    duelRound += 1
                    if duelScore[w] >= 5:
                        fx({'k': 'duelend', 'winner': w, 'score': dict(duelScore)})
                        duelWinner = w
                        duelEndT = 7.0
                        duelScore = {}
                        duelRound = 1

def enemyPool():
    lo = max(1, wave - 1); hi = min(8, wave + 1)
    ids = [k for k, v in VEH.items() if v['tier'] >= lo and v['tier'] <= hi]
    return ids[random.randrange(len(ids))] if ids else 'ussr_light_1'

def spawnEnemy():
    live = [u for u in units if u['team'] == 'player' and u['al']]
    for _ in range(30):
        side = random.randrange(4)
        if side == 0: x = random.uniform(80, ARENA_W - 80); z = random.uniform(80, 200)
        elif side == 1: x = random.uniform(80, ARENA_W - 80); z = ARENA_H - random.uniform(80, 200)
        elif side == 2: x = random.uniform(80, 200); z = random.uniform(80, ARENA_H - 80)
        else: x = ARENA_W - random.uniform(80, 200); z = random.uniform(80, ARENA_H - 80)
        if live and min(math.hypot(x - p['x'], z - p['z']) for p in live) < 500:
            continue
        break
    m = {
        'hp': 1 + (wave - 1) * 0.12, 'dmg': 0.35 + (wave - 1) * 0.03,
        'cd': max(2.0, 3.4 * (0.93 ** (wave - 1))), 'speed': 1 + min(0.35, (wave - 1) * 0.04)
    }
    t = newUnit(enemyPool(), 'enemy', x, z)
    v = t['v']
    t['sp'] = v['speed'] * m['speed']
    t['hp'] = t['mh'] = round(v['hp'] * m['hp'])
    t['dmg'] = v['dmg'] * m['dmg']
    t['cd'] = max(0.6, v['cd'] * m['cd'])
    t['rev'] = False
    units.append(t)

def updateAI(t, dt):
    ai = t['ai']
    tgt = None; d = 1e9
    for o in units:
        if not o['al'] or o is t: continue
        if t['team'] == 'enemy' and o['team'] != 'player': continue
        dd = math.hypot(o['x'] - t['x'], o['z'] - t['z'])
        if dd < d: d = dd; tgt = o
    v = t['v']
    ai['t'] -= dt
    # антизастревание
    ai['stuckT'] = ai.get('stuckT', 0) + dt
    if abs(t['x'] - ai.get('lx', t['x'])) + abs(t['z'] - ai.get('lz', t['z'])) > 4:
        ai['lx'] = t['x']; ai['lz'] = t['z']; ai['stuckT'] = 0
    if ai['stuckT'] > 1.6:
        ai['evade'] = random.uniform(0, 6.28); ai['evadeT'] = random.uniform(0.8, 1.6)
        ai['stuckT'] = 0; ai['lx'] = t['x']; ai['lz'] = t['z']
    if ai.get('evadeT', 0) > 0: ai['evadeT'] -= dt
    if not tgt:
        t['tu'] = rotateToward(t['tu'], t['a'], v['turretSpeed'] * DEG * dt)
        return
    goal = math.atan2(tgt['z'] - t['z'], tgt['x'] - t['x'])
    pref = PREF_DIST.get(v['type'], 330)
    if d > pref + 240: moveDir = goal
    elif d < pref - 80: moveDir = goal + math.pi
    else:
        ai['weaveT'] -= dt
        if ai['weaveT'] <= 0:
            ai['weave'] = random.uniform(-0.5, 0.5); ai['weaveT'] = random.uniform(0.7, 1.5)
        moveDir = goal + ai.get('weave', 0)
    look = 90
    px = t['x'] + math.cos(moveDir) * look; pz = t['z'] + math.sin(moveDir) * look
    if wallBlocking(px, pz, TANK_R) or any(o is not t and o['al'] and
            math.hypot(px - o['x'], pz - o['z']) < TANK_R * 2 for o in units):
        moveDir += math.pi / 2 * (ai['strafeDir'] or 1)
    t['a'] = rotateToward(t['a'], moveDir, v['hullSpeed'] * DEG * dt)
    inRange = d < 950
    if inRange: ai['aimErr'] = max(0.08, ai['aimErr'] - dt * 0.6)
    else: ai['aimErr'] = min(0.9, ai['aimErr'] + dt * 0.5)
    err = ai['aimErr'] * random.uniform(-1, 1) + (0.12 if d > 600 else 0.02)
    gunTarget = goal + err
    if v.get('sector'):
        rel = clamp(angNorm(gunTarget - t['a']), -60 * DEG, 60 * DEG)
        gunTarget = t['a'] + rel
    t['tu'] = rotateToward(t['tu'], gunTarget, v['turretSpeed'] * DEG * dt)
    updateMagT(t, dt)
    aimed = abs(angNorm(t['tu'] - gunTarget)) < 0.1
    if aimed and inRange and canFireT(t) and random.random() < dt * 2.2:
        fireDirect(t, 0.02)
    sx = t['x'] + math.cos(moveDir) * t['sp'] * dt
    sz = t['z'] + math.sin(moveDir) * t['sp'] * dt
    if not wallBlocking(sx, sz, TANK_R - 2):
        t['x'] = sx; t['z'] = sz; t['wi'] = t['sp']
    else:
        t['wi'] = 0
    resolveTankWalls(t)

def tick(dt):
    global wave, waveTimer, sseq, bullets, duelEndT, duelWinner
    # таймер сброса после конца матча дуэли
    if duelEndT > 0:
        duelEndT -= dt
        if duelEndT <= 0:
            duelEndT = 0; duelWinner = None
    livePlayers = [p for p in players.values() if p['al']]
    # игроки: respawn
    for p in players.values():
        if not p['al']:
            p['respawnT'] = p.get('respawnT', 4.0) - dt
            if p['respawnT'] <= 0:
                p['al'] = True; p['hp'] = p['mh']
                if worldMode == 'duel':
                    x, z, a = duelSpawn(p.get('side', 1))
                    p['x'], p['z'], p['a'], p['tu'] = x, z, a, a
                else:
                    p['x'], p['z'] = ARENA_W / 2 + random.uniform(-120, 120), ARENA_H / 2 + random.uniform(-120, 120)
                resolveTankWalls(p)
                fx({'k': 'respawn', 'i': p['id']})
    # ИИ врагов
    for u in units:
        if u['al'] and u['ai']: updateAI(u, dt)
    for p in players.values():
        p['recoil'] = max(0, p['recoil'] - dt * 5)
    resolvePairs()
    for u in units: resolveTankWalls(u)
    # снаряды
    for b in bullets:
        if b.get('dead'): continue
        b['x'] += b['vx'] * dt; b['y'] += b['vy'] * dt; b['z'] += b['vz'] * dt
        b['life'] -= dt
        if b['life'] <= 0: b['dead'] = True; continue
        hit = False
        for w in walls:
            wH = heightAt(w['x'] + w['w'] / 2, w['y'] + w['h'] / 2)
            if circleRectHit(b['x'], b['z'], 6, w['x'], w['y'], w['w'], w['h']) and b['y'] < wH + 70:
                if w.get('crate'):
                    w['hp'] = w.get('hp', 2) - 1
                    if w['hp'] <= 0:
                        walls.remove(w)
                        fx({'k': 'boom', 'x': b['x'], 'z': b['z']})
                else:
                    fx({'k': 'spark', 'x': b['x'], 'y': b['y'], 'z': b['z'], 'c': 'grey'})
                hit = True; break
        if hit: b['dead'] = True; continue
        for t in units:
            if not t['al']: continue
            if b.get('from') and b['from'] == t['id']: continue
            if worldMode == 'duel':
                if t['team'] != 'player' or b['team'] != 'player': continue
            else:
                if t['team'] == b['team']: continue
            tH = heightAt(t['x'], t['z'])
            if math.hypot(b['x'] - t['x'], b['z'] - t['z']) < TANK_R + 12 and tH - 4 < b['y'] < tH + 60:
                zi = zoneOf(b['x'], b['z'], t)
                roll = b['pen'] * random.uniform(0.85, 1.15)
                if roll >= t['armor'][zi]:
                    damage(t, b['dmg'], b['x'], b['y'], b['z'], b['team'])
                    fx({'k': 'spark', 'x': b['x'], 'y': b['y'], 'z': b['z'], 'c': 'gold'})
                else:
                    damage(t, b['dmg'] * 0.15, b['x'], b['y'], b['z'], b['team'])
                    fx({'k': 'spark', 'x': b['x'], 'y': b['y'], 'z': b['z'], 'c': 'grey'})
                b['dead'] = True
                break
        if not b.get('dead') and b['y'] < heightAt(b['x'], b['z']) + 1:
            fx({'k': 'boom', 'x': b['x'], 'z': b['z']})
            b['dead'] = True
    bullets = [b for b in bullets if not b.get('dead')]
    # удалить мёртвых врагов из списка (через 3.5с можно все)
    # волны (только в коопе; в дуэли врагов нет)
    if worldMode != 'duel' and not any(u['team'] == 'enemy' and u['al'] for u in units):
        waveTimer -= dt
        if waveTimer <= 0:
            wave += 1
            n = round((2 + wave) * (ARENA_W * ARENA_H) / (2400 * 1600))
            for _ in range(n): spawnEnemy()
            waveTimer = 3.5
            fx({'k': 'wave', 'w': wave})
    # убрать мёртвых врагов (игроки остаются — их respawn ниже)
    units[:] = [u for u in units if u['al'] or u['team'] == 'player']
    sseq += 1

# ---------------- события/рассылка ----------------
fxs = []   # очередь fx-событий в этом тике
def fx(e):
    fxs.append(e)

def stSnapshot():
    pts = []
    for u in units:
        pts.append({
            'i': u['id'], 'v': u['veh'], 'tm': u['team'],
            'x': round(u['x'], 1), 'z': round(u['z'], 1),
            'a': round(u['a'], 3), 'tu': round(u['tu'], 3), 'el': round(u['el'], 3),
            'h': round(u['hp']), 'mh': u['mh'], 'al': u['al']
        })
    bs = [{'i': b['id'], 'x': round(b['x'], 1), 'y': round(b['y'], 1), 'z': round(b['z'], 1)}
          for b in bullets]
    gm = {'m': worldMode, 's': dict(duelScore), 'r': duelRound, 'w': duelWinner}
    return {'t': 'st', 'n': sseq, 'w': wave, 'gm': gm, 'pts': pts, 'bs': bs}

async def send(ws, obj):
    try:
        await ws_send(ws['w'], json.dumps(obj, ensure_ascii=False))
    except Exception:
        pass

async def broadcast(obj):
    for rw in list(players.keys()):
        await send({'w': rw[1]}, obj)

# ---------------- WebSocket (минимальный RFC6455) ----------------
MAGIC = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11'

async def handshake(reader, writer):
    data = b''
    while b'\r\n\r\n' not in data:
        chunk = await reader.read(4096)
        if not chunk: return None
        data += chunk
        if len(data) > 16384: return None
    head = data.split(b'\r\n\r\n')[0].decode('latin1')
    key = None
    for line in head.split('\r\n'):
        if line.lower().startswith('sec-websocket-key:'):
            key = line.split(':', 1)[1].strip()
    if not key: return None
    accept = base64.b64encode(hashlib.sha1((key + MAGIC).encode()).digest()).decode()
    resp = ('HTTP/1.1 101 Switching Protocols\r\n'
            'Upgrade: websocket\r\n'
            'Connection: Upgrade\r\n'
            'Sec-WebSocket-Accept: ' + accept + '\r\n\r\n')
    writer.write(resp.encode('latin1'))
    await writer.drain()
    return key

async def recv_exact(reader, n):
    data = b''
    while len(data) < n:
        chunk = await reader.read(n - len(data))
        if not chunk: return None
        data += chunk
    return data

async def ws_recv(reader):
    h = await recv_exact(reader, 2)
    if h is None: return None
    opcode = h[0] & 0x0F
    ln = h[1] & 0x7F
    masked = h[1] & 0x80
    if ln == 126:
        ext = await recv_exact(reader, 2)
        if ext is None: return None
        ln = struct.unpack('>H', ext)[0]
    elif ln == 127:
        ext = await recv_exact(reader, 8)
        if ext is None: return None
        ln = struct.unpack('>Q', ext)[0]
    if ln > 200000: return None
    mask = await recv_exact(reader, 4) if masked else None
    payload = await recv_exact(reader, ln)
    if payload is None: return None
    if mask:
        payload = bytes(b ^ mask[i % 4] for i, b in enumerate(payload))
    return opcode, payload

async def ws_send(writer, payload):
    if isinstance(payload, str): payload = payload.encode('utf-8')
    ln = len(payload)
    if ln < 126:
        writer.write(bytes([0x81, ln]) + payload)
    elif ln < 65536:
        writer.write(bytes([0x81, 126]) + struct.pack('>H', ln) + payload)
    else:
        writer.write(bytes([0x81, 127]) + struct.pack('>Q', ln) + payload)
    await writer.drain()

# ---------------- клиенты ----------------
async def handle(reader, writer):
    global sseq, worldMode, duelScore, duelRound, duelWinner, duelEndT
    ws = None
    try:
        key = await handshake(reader, writer)
        if key is None:
            writer.close(); return
        ws = {'r': reader, 'w': writer}
        unit = None
        while True:
            msg = await ws_recv(reader)
            if msg is None: break
            opcode, payload = msg
            if opcode == 8: break            # close
            if opcode == 9:                  # ping
                await ws_send(writer, b'\x8a' + payload)
                continue
            if opcode in (10,): continue     # pong
            if opcode != 1: continue
            try:
                data = json.loads(payload.decode('utf-8'))
            except Exception:
                continue
            tp = data.get('t')
            if tp == 'join':
                vehId = data.get('veh')
                if vehId not in VEH: vehId = 'ussr_medium_3'
                mode = data.get('mode')
                side = 1
                if mode == 'duel':
                    # сервер занят другой игрой или дуэль полная — отказ
                    if players and worldMode != 'duel':
                        await send(ws, {'t': 'busy'}); continue
                    if worldMode == 'duel' and len(players) >= 2:
                        await send(ws, {'t': 'full'}); continue
                    worldMode = 'duel'
                    side = 0 if not any(u.get('side') == 0 for u in units if u['team'] == 'player') else 1
                    x, z, a = duelSpawn(side)
                else:
                    if worldMode == 'duel' and players:
                        await send(ws, {'t': 'busy'}); continue
                    worldMode = 'coop'
                    # свободное место у центра
                    x, z = ARENA_W / 2, ARENA_H / 2
                    for _ in range(40):
                        x = ARENA_W / 2 + random.uniform(-260, 260)
                        z = ARENA_H / 2 + random.uniform(-200, 200)
                        if not wallBlocking(x, z, TANK_R + 4) and not any(
                                u is not (unit) and u['al'] and math.hypot(u['x'] - x, u['z'] - z) < TANK_R * 3
                                for u in units if u['team'] == 'player'):
                            break
                    a = 0
                unit = newUnit(vehId, 'player', x, z, a=a)
                unit['id'] = 'p' + str(id(unit))
                unit['side'] = side
                players[(reader, writer)] = unit
                units.append(unit)
                await send(ws, {'t': 'init', 'self': unit['id'],
                                'gm': {'m': worldMode, 's': dict(duelScore), 'r': duelRound, 'w': duelWinner},
                                'map': {'id': 'field', 'w': ARENA_W, 'h': ARENA_H,
                                        'hills': [],
                                        'walls': [{'x': w['x'], 'y': w['y'], 'w': w['w'], 'h': w['h'],
                                                   'crate': bool(w.get('crate'))} for w in walls]}})
                fx({'k': 'wave', 'w': wave})
                continue
            if tp == 'in' and unit:
                unit['x'] = float(data.get('x', unit['x']))
                unit['z'] = float(data.get('z', unit['z']))
                unit['a'] = float(data.get('a', unit['a']))
                unit['tu'] = float(data.get('tu', unit['tu']))
                unit['el'] = float(data.get('el', unit['el']))
                resolveTankWalls(unit)
                if data.get('f') and unit['al'] and canFireT(unit):
                    fireDirect(unit, unit['el'])
                continue
            if tp == 'respawn' and unit and not unit['al']:
                unit['al'] = True; unit['hp'] = unit['mh']
                if worldMode == 'duel':
                    x, z, a = duelSpawn(unit.get('side', 1))
                    unit['x'], unit['z'], unit['a'], unit['tu'] = x, z, a, a
                else:
                    unit['x'], unit['z'] = ARENA_W / 2, ARENA_H / 2
                resolveTankWalls(unit)
                fx({'k': 'respawn', 'i': unit['id']})
                continue
    except (ConnectionError, asyncio.CancelledError):
        pass
    except Exception as e:
        import traceback
        print('HANDLE ERR:', e)
        traceback.print_exc()
    finally:
        pkey = (reader, writer)
        if pkey in players:
            unit = players.pop(pkey)
            if unit in units: units.remove(unit)
        # если дуэль опустела — режим сбрасывается в кооп
        if worldMode == 'duel' and not any(u['team'] == 'player' for u in units):
            worldMode = 'coop'
            duelScore = {}; duelRound = 1; duelWinner = None; duelEndT = 0
        try:
            writer.close()
        except Exception:
            pass

async def loop():
    last = time.time()
    while True:
        # раздать fx-события сразу
        if fxs:
            n = sseq
            for e in fxs:
                e['n'] = n
            await broadcast({'t': 'fxs', 'items': fxs})
            fxs.clear()
        dt = max(0.0, min(0.05, time.time() - last))
        last = time.time()
        tick(dt)
        await broadcast(stSnapshot())
        await asyncio.sleep(0.02)   # 50 Гц

async def main():
    genWalls()
    server = await asyncio.start_server(handle, '0.0.0.0', PORT)
    print('Танковый сервер: порт', PORT)
    async with server:
        await asyncio.gather(server.serve_forever(), loop())

if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass