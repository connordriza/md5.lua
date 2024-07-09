local md5 = {
  _VERSION     = "md5.lua 1.1.0",
  _DESCRIPTION = "MD5 computation in Lua (5.1-3, LuaJIT)",
  _URL         = "https://github.com/kikito/md5.lua",
  _LICENSE     = [[
    MIT LICENSE

    Copyright (c) 2013 Enrique García Cota + Adam Baldwin + hanzao + Equi 4 Software

    Permission is hereby granted, free of charge, to any person obtaining a
    copy of this software and associated documentation files (the
    "Software"), to deal in the Software without restriction, including
    without limitation the rights to use, copy, modify, merge, publish,
    distribute, sublicense, and/or sell copies of the Software, and to
    permit persons to whom the Software is furnished to do so, subject to
    the following conditions:

    The above copyright notice and this permission notice shall be included
    in all copies or substantial portions of the Software.

    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
    OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
    IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
    CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
    TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
    SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
  ]]
}

-- bit lib implementions

local char, byte, format, rep, sub =
  string.char, string.byte, string.format, string.rep, string.sub
local bit_or, bit_and, bit_not, bit_xor, bit_rshift, bit_lshift

local ok, bit = pcall(require, 'bit')
local ok_ffi, ffi = pcall(require, 'ffi')
if ok then
  bit_or, bit_and, bit_not, bit_xor, bit_rshift, bit_lshift = bit.bor, bit.band, bit.bnot, bit.bxor, bit.rshift, bit.lshift
else
  ok, bit = pcall(require, 'bit32')

  if ok then

    bit_not = bit.bnot

    local tobit = function(n)
      return n <= 0x7fffffff and n or -(bit_not(n) + 1)
    end

    local normalize = function(f)
      return function(a,b) return tobit(f(tobit(a), tobit(b))) end
    end

    bit_or, bit_and, bit_xor = normalize(bit.bor), normalize(bit.band), normalize(bit.bxor)
    bit_rshift, bit_lshift = normalize(bit.rshift), normalize(bit.lshift)

  else

    local function tbl2number(tbl)
      local result = 0
      local power = 1
      for i = 1, #tbl do
        result = result + tbl[i] * power
        power = power * 2
      end
      return result
    end

    local function expand(t1, t2)
      local big, small = t1, t2
      if(#big < #small) then
        big, small = small, big
      end
      -- expand small
      for i = #small + 1, #big do
        small[i] = 0
      end
    end

    local to_bits -- needs to be declared before bit_not

    bit_not = function(n)
      local tbl = to_bits(n)
      local size = math.max(#tbl, 32)
      for i = 1, size do
        if(tbl[i] == 1) then
          tbl[i] = 0
        else
          tbl[i] = 1
        end
      end
      return tbl2number(tbl)
    end

    -- defined as local above
    to_bits = function (n)
      if(n < 0) then
        -- negative
        return to_bits(bit_not(math.abs(n)) + 1)
      end
      -- to bits table
      local tbl = {}
      local cnt = 1
      local last
      while n > 0 do
        last      = n % 2
        tbl[cnt]  = last
        n         = (n-last)/2
        cnt       = cnt + 1
      end

      return tbl
    end

    bit_or = function(m, n)
      local tbl_m = to_bits(m)
      local tbl_n = to_bits(n)
      expand(tbl_m, tbl_n)

      local tbl = {}
      for i = 1, #tbl_m do
        if(tbl_m[i]== 0 and tbl_n[i] == 0) then
          tbl[i] = 0
        else
          tbl[i] = 1
        end
      end

      return tbl2number(tbl)
    end

    bit_and = function(m, n)
      local tbl_m = to_bits(m)
      local tbl_n = to_bits(n)
      expand(tbl_m, tbl_n)

      local tbl = {}
      for i = 1, #tbl_m do
        if(tbl_m[i]== 0 or tbl_n[i] == 0) then
          tbl[i] = 0
        else
          tbl[i] = 1
        end
      end

      return tbl2number(tbl)
    end

    bit_xor = function(m, n)
      local tbl_m = to_bits(m)
      local tbl_n = to_bits(n)
      expand(tbl_m, tbl_n)

      local tbl = {}
      for i = 1, #tbl_m do
        if(tbl_m[i] ~= tbl_n[i]) then
          tbl[i] = 1
        else
          tbl[i] = 0
        end
      end

      return tbl2number(tbl)
    end

    bit_rshift = function(n, bits)
      local high_bit = 0
      if(n < 0) then
        -- negative
        n = bit_not(math.abs(n)) + 1
        high_bit = 0x80000000
      end

      local floor = math.floor

      for i=1, bits do
        n = n/2
        n = bit_or(floor(n), high_bit)
      end
      return floor(n)
    end

    bit_lshift = function(n, bits)
      if(n < 0) then
        -- negative
        n = bit_not(math.abs(n)) + 1
      end

      for i=1, bits do
        n = n*2
      end
      return bit_and(n, 0xFFFFFFFF)
    end
  end
end

-- convert little-endian 32-bit int to a 4-char string
local lei2str
-- function is defined this way to allow full jit compilation (removing UCLO instruction in LuaJIT)
if ok_ffi then
  local ct_IntType = ffi.typeof("int[1]")
  lei2str = function(i) return ffi.string(ct_IntType(i), 4) end
else
  lei2str = function (i)
    local f=function (s) return char( bit_and( bit_rshift(i, s), 255)) end
    return f(0)..f(8)..f(16)..f(24)
  end
end

-- convert raw string to big-endian int
local function str2bei(s)
  local v=0
  for i=1, #s do
    v = v * 256 + byte(s, i)
  end
  return v
end

-- convert raw string to little-endian int
local str2lei

if ok_ffi then
  local ct_constcharptr = ffi.typeof("const char*")
  local ct_constintptr = ffi.typeof("const int*")
  str2lei = function(s)
    local int = ct_constcharptr(s)
    return ffi.cast(ct_constintptr, int)[0]
  end
else
  str2lei = function(s)
    local v=0
    for i = #s,1,-1 do
      v = v*256 + byte(s, i)
    end
    return v
    end
end

-- cut up a string in little-endian ints of given size
local function cut_le_str(s)
  local tmp = {};
  for i = 1, 16 do
    local arg = i * 4
    tmp[i] = str2lei(sub(s, arg - 3, arg))
  end

  return tmp
end

-- An MD5 mplementation in Lua, requires bitlib (hacked to use LuaBit from above, ugh)
-- 10/02/2001 jcw@equi4.com

local CONSTS = {
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee,
  0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be,
  0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa,
  0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed,
  0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c,
  0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05,
  0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039,
  0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1,
  0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391,
  0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476
}

local md5_transform_funcs = {
    [1] = function(x, y, z) return bit.bor(bit.band(x, y), bit.band(-x - 1, z)) end,
    [2] = function(x, y, z) return bit.bor(bit.band(x, z), bit.band(y, -z - 1)) end,
    [3] = function(x, y, z) return bit.bxor(x, bit.bxor(y, z)) end,
    [4] = function(x, y, z) return bit.bxor(y, bit.bor(x, -z - 1)) end
}

local z=function (ff,a,b,c,d,x,s,ac)
  a=bit_and(a+ff(b,c,d)+x+ac,0xFFFFFFFF)
  -- be *very* careful that left shift does not cause rounding!
  return bit_or(bit_lshift(bit_and(a,bit_rshift(0xFFFFFFFF,s)),s),bit_rshift(a,32-s))+b
end

local md5_sTab = {
  {7, 12, 17, 22},
  {5, 9, 14, 20},
  {4, 11, 16, 23},
  {6, 10, 15, 21},
}

local md5_xTab = {
  {1, 6, 11, 0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12},
  {5, 8, 11, 14, 1, 4, 7, 10, 13, 0, 3, 6, 9, 12, 15, 2},
  {0, 7, 14, 5, 12, 3, 10, 1, 8, 15, 6, 13, 4, 11, 2, 9}
}

local md5_setOrder = {
  1,
  4,
  3,
  2
}

function transform(A, B, C, D, X)
  local tab = {A, B, C, D};
  local argsOrder = {1, 2, 3, 4}
  local function carousel()
    local tmp = {}
    tmp[1] = argsOrder[4]
    tmp[2] = argsOrder[1]
    tmp[3] = argsOrder[2]
    tmp[4] = argsOrder[3]
    return tmp;
  end

  for i = 0, 63 do
    local chunk = math.floor(i / 16) + 1;
    local xIndex = (i <= 15) and i or md5_xTab[chunk - 1][(i % 16) + 1];
    local x = X[xIndex];
    local current = (i % 4) + 1;
    local s = md5_sTab[chunk][current];
    tab[md5_setOrder[current]] = z(md5_transform_funcs[chunk], tab[argsOrder[1]], tab[argsOrder[2]], tab[argsOrder[3]], tab[argsOrder[4]], x, s, CONSTS[i + 1])
    argsOrder = carousel();
  end

  return bit_and(A+tab[1],0xFFFFFFFF),bit_and(B+tab[2],0xFFFFFFFF),
    bit_and(C+tab[3],0xFFFFFFFF),bit_and(D+tab[4],0xFFFFFFFF)
end
----------------------------------------------------------------

local function md5_update(self, s)
  self.pos = self.pos + #s
  s = self.buf .. s
  for ii = 1, #s - 63, 64 do
    local X = cut_le_str(sub(s,ii,ii+63))
    assert(#X == 16)
    X[0] = table.remove(X,1) -- zero based!
    self.a,self.b,self.c,self.d = transform(self.a,self.b,self.c,self.d,X)
  end

  self.buf = sub(s, math.floor(#s/64)*64 + 1, #s)
  return self
end

local function md5_finish(self)
  local msgLen = self.pos
  local padLen = 56 - msgLen % 64
  if msgLen % 64 > 56 then padLen = padLen + 64 end
  if padLen == 0 then padLen = 64 end
  local s = char(128) .. rep(char(0),padLen-1) .. lei2str(bit_and(8*msgLen, 0xFFFFFFFF)) .. lei2str(math.floor(msgLen/0x20000000))
  md5_update(self, s)
  assert(self.pos % 64 == 0)
  return lei2str(self.a) .. lei2str(self.b) .. lei2str(self.c) .. lei2str(self.d)
end

----------------------------------------------------------------

function md5.new()
  return { a = CONSTS[65], b = CONSTS[66], c = CONSTS[67], d = CONSTS[68],
           pos = 0,
           buf = '',
           update = md5_update,
           finish = md5_finish }
end

function md5.tohex(s)
  local tb = {}
  for i = 1..8
  do
    arg = i * 2
    tb[i] = format("%04x", str2bei(sub(s, arg - 1, arg)))
  end
  return tb:concat()
end

function md5.sum(s)
  return md5.new():update(s):finish()
end

function md5.sumhexa(s)
  return md5.tohex(md5.sum(s))
end

return md5
