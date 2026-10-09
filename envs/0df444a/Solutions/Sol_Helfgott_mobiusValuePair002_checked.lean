-- Prove2me | solution 1 for Helfgott.mobiusValuePair002_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T21:52:23.781063+00:00
-- url     : https://prove2.me/submissions/bd1dbd9c-fcbc-45f2-bbf1-f91b7a15912c

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Mathlib.Tactic


set_option autoImplicit false
namespace Helfgott

lemma mobiusTreeCheck_join (g : ℕ → ℤ) (B d offset : ℕ) (l r : MobiusCertTree)
    (hl : mobiusTreeCheck g B d offset l = true)
    (hr : mobiusTreeCheck g B d (offset + 32 * 2 ^ d) r = true) :
    mobiusTreeCheck g B (d + 1) offset (.branch l r) = true := by
  by_cases hoff : B ≤ offset
  · simp [mobiusTreeCheck, hoff]
  · simpa [mobiusTreeCheck, hoff] using And.intro hl hr

lemma mobiusHarmonicTreeCheck_join (g M : ℕ → ℤ) (Q B d offset upper : ℕ)
    (l r : MobiusHarmonicTree) (hoff : offset < B)
    (hl : mobiusHarmonicTreeCheck g M Q B d offset l = true)
    (hr : mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r = true)
    (hu : upper = mobiusHarmonicUpper l + mobiusHarmonicUpper r) :
    mobiusHarmonicTreeCheck g M Q B (d + 1) offset (.branch upper l r) = true := by
  have hoff' : ¬B ≤ offset := not_le.mpr hoff
  simpa [mobiusHarmonicTreeCheck, hoff', Bool.and_assoc, and_assoc] using ⟨hl, hr, hu⟩

end Helfgott
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Helfgott

private abbrev cg : ℕ → ℤ := mobiusTreeValue 16 mobiusTable1200001

private def publishedLeaf : ℕ → MobiusCertTree → ℕ → MobiusCertTree
  | 0, tree, _ => tree
  | d + 1, .branch l r, k =>
      if k < 2 ^ d then publishedLeaf d l k else publishedLeaf d r (k - 2 ^ d)
  | _, tree, _ => tree

private abbrev d8 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 0
private theorem p8 : mobiusTreeCheck cg 1200001 1 32768 d8 = true := by decide +kernel

private abbrev d9 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 1
private theorem p9 : mobiusTreeCheck cg 1200001 1 32832 d9 = true := by decide +kernel

private def d7 : MobiusCertTree := .branch d8 d9
private abbrev d11 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 2
private theorem p11 : mobiusTreeCheck cg 1200001 1 32896 d11 = true := by decide +kernel

private abbrev d12 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 3
private theorem p12 : mobiusTreeCheck cg 1200001 1 32960 d12 = true := by decide +kernel

private def d10 : MobiusCertTree := .branch d11 d12
private def d6 : MobiusCertTree := .branch d7 d10
private abbrev d15 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 4
private theorem p15 : mobiusTreeCheck cg 1200001 1 33024 d15 = true := by decide +kernel

private abbrev d16 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 5
private theorem p16 : mobiusTreeCheck cg 1200001 1 33088 d16 = true := by decide +kernel

private def d14 : MobiusCertTree := .branch d15 d16
private abbrev d18 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 6
private theorem p18 : mobiusTreeCheck cg 1200001 1 33152 d18 = true := by decide +kernel

private abbrev d19 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 7
private theorem p19 : mobiusTreeCheck cg 1200001 1 33216 d19 = true := by decide +kernel

private def d17 : MobiusCertTree := .branch d18 d19
private def d13 : MobiusCertTree := .branch d14 d17
private def d5 : MobiusCertTree := .branch d6 d13
private abbrev d23 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 8
private theorem p23 : mobiusTreeCheck cg 1200001 1 33280 d23 = true := by decide +kernel

private abbrev d24 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 9
private theorem p24 : mobiusTreeCheck cg 1200001 1 33344 d24 = true := by decide +kernel

private def d22 : MobiusCertTree := .branch d23 d24
private abbrev d26 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 10
private theorem p26 : mobiusTreeCheck cg 1200001 1 33408 d26 = true := by decide +kernel

private abbrev d27 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 11
private theorem p27 : mobiusTreeCheck cg 1200001 1 33472 d27 = true := by decide +kernel

private def d25 : MobiusCertTree := .branch d26 d27
private def d21 : MobiusCertTree := .branch d22 d25
private abbrev d30 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 12
private theorem p30 : mobiusTreeCheck cg 1200001 1 33536 d30 = true := by decide +kernel

private abbrev d31 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 13
private theorem p31 : mobiusTreeCheck cg 1200001 1 33600 d31 = true := by decide +kernel

private def d29 : MobiusCertTree := .branch d30 d31
private abbrev d33 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 14
private theorem p33 : mobiusTreeCheck cg 1200001 1 33664 d33 = true := by decide +kernel

private abbrev d34 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 15
private theorem p34 : mobiusTreeCheck cg 1200001 1 33728 d34 = true := by decide +kernel

private def d32 : MobiusCertTree := .branch d33 d34
private def d28 : MobiusCertTree := .branch d29 d32
private def d20 : MobiusCertTree := .branch d21 d28
private def d4 : MobiusCertTree := .branch d5 d20
private abbrev d39 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 16
private theorem p39 : mobiusTreeCheck cg 1200001 1 33792 d39 = true := by decide +kernel

private abbrev d40 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 17
private theorem p40 : mobiusTreeCheck cg 1200001 1 33856 d40 = true := by decide +kernel

private def d38 : MobiusCertTree := .branch d39 d40
private abbrev d42 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 18
private theorem p42 : mobiusTreeCheck cg 1200001 1 33920 d42 = true := by decide +kernel

private abbrev d43 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 19
private theorem p43 : mobiusTreeCheck cg 1200001 1 33984 d43 = true := by decide +kernel

private def d41 : MobiusCertTree := .branch d42 d43
private def d37 : MobiusCertTree := .branch d38 d41
private abbrev d46 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 20
private theorem p46 : mobiusTreeCheck cg 1200001 1 34048 d46 = true := by decide +kernel

private abbrev d47 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 21
private theorem p47 : mobiusTreeCheck cg 1200001 1 34112 d47 = true := by decide +kernel

private def d45 : MobiusCertTree := .branch d46 d47
private abbrev d49 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 22
private theorem p49 : mobiusTreeCheck cg 1200001 1 34176 d49 = true := by decide +kernel

private abbrev d50 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 23
private theorem p50 : mobiusTreeCheck cg 1200001 1 34240 d50 = true := by decide +kernel

private def d48 : MobiusCertTree := .branch d49 d50
private def d44 : MobiusCertTree := .branch d45 d48
private def d36 : MobiusCertTree := .branch d37 d44
private abbrev d54 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 24
private theorem p54 : mobiusTreeCheck cg 1200001 1 34304 d54 = true := by decide +kernel

private abbrev d55 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 25
private theorem p55 : mobiusTreeCheck cg 1200001 1 34368 d55 = true := by decide +kernel

private def d53 : MobiusCertTree := .branch d54 d55
private abbrev d57 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 26
private theorem p57 : mobiusTreeCheck cg 1200001 1 34432 d57 = true := by decide +kernel

private abbrev d58 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 27
private theorem p58 : mobiusTreeCheck cg 1200001 1 34496 d58 = true := by decide +kernel

private def d56 : MobiusCertTree := .branch d57 d58
private def d52 : MobiusCertTree := .branch d53 d56
private abbrev d61 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 28
private theorem p61 : mobiusTreeCheck cg 1200001 1 34560 d61 = true := by decide +kernel

private abbrev d62 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 29
private theorem p62 : mobiusTreeCheck cg 1200001 1 34624 d62 = true := by decide +kernel

private def d60 : MobiusCertTree := .branch d61 d62
private abbrev d64 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 30
private theorem p64 : mobiusTreeCheck cg 1200001 1 34688 d64 = true := by decide +kernel

private abbrev d65 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 31
private theorem p65 : mobiusTreeCheck cg 1200001 1 34752 d65 = true := by decide +kernel

private def d63 : MobiusCertTree := .branch d64 d65
private def d59 : MobiusCertTree := .branch d60 d63
private def d51 : MobiusCertTree := .branch d52 d59
private def d35 : MobiusCertTree := .branch d36 d51
private def d3 : MobiusCertTree := .branch d4 d35
private abbrev d71 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 32
private theorem p71 : mobiusTreeCheck cg 1200001 1 34816 d71 = true := by decide +kernel

private abbrev d72 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 33
private theorem p72 : mobiusTreeCheck cg 1200001 1 34880 d72 = true := by decide +kernel

private def d70 : MobiusCertTree := .branch d71 d72
private abbrev d74 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 34
private theorem p74 : mobiusTreeCheck cg 1200001 1 34944 d74 = true := by decide +kernel

private abbrev d75 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 35
private theorem p75 : mobiusTreeCheck cg 1200001 1 35008 d75 = true := by decide +kernel

private def d73 : MobiusCertTree := .branch d74 d75
private def d69 : MobiusCertTree := .branch d70 d73
private abbrev d78 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 36
private theorem p78 : mobiusTreeCheck cg 1200001 1 35072 d78 = true := by decide +kernel

private abbrev d79 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 37
private theorem p79 : mobiusTreeCheck cg 1200001 1 35136 d79 = true := by decide +kernel

private def d77 : MobiusCertTree := .branch d78 d79
private abbrev d81 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 38
private theorem p81 : mobiusTreeCheck cg 1200001 1 35200 d81 = true := by decide +kernel

private abbrev d82 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 39
private theorem p82 : mobiusTreeCheck cg 1200001 1 35264 d82 = true := by decide +kernel

private def d80 : MobiusCertTree := .branch d81 d82
private def d76 : MobiusCertTree := .branch d77 d80
private def d68 : MobiusCertTree := .branch d69 d76
private abbrev d86 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 40
private theorem p86 : mobiusTreeCheck cg 1200001 1 35328 d86 = true := by decide +kernel

private abbrev d87 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 41
private theorem p87 : mobiusTreeCheck cg 1200001 1 35392 d87 = true := by decide +kernel

private def d85 : MobiusCertTree := .branch d86 d87
private abbrev d89 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 42
private theorem p89 : mobiusTreeCheck cg 1200001 1 35456 d89 = true := by decide +kernel

private abbrev d90 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 43
private theorem p90 : mobiusTreeCheck cg 1200001 1 35520 d90 = true := by decide +kernel

private def d88 : MobiusCertTree := .branch d89 d90
private def d84 : MobiusCertTree := .branch d85 d88
private abbrev d93 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 44
private theorem p93 : mobiusTreeCheck cg 1200001 1 35584 d93 = true := by decide +kernel

private abbrev d94 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 45
private theorem p94 : mobiusTreeCheck cg 1200001 1 35648 d94 = true := by decide +kernel

private def d92 : MobiusCertTree := .branch d93 d94
private abbrev d96 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 46
private theorem p96 : mobiusTreeCheck cg 1200001 1 35712 d96 = true := by decide +kernel

private abbrev d97 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 47
private theorem p97 : mobiusTreeCheck cg 1200001 1 35776 d97 = true := by decide +kernel

private def d95 : MobiusCertTree := .branch d96 d97
private def d91 : MobiusCertTree := .branch d92 d95
private def d83 : MobiusCertTree := .branch d84 d91
private def d67 : MobiusCertTree := .branch d68 d83
private abbrev d102 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 48
private theorem p102 : mobiusTreeCheck cg 1200001 1 35840 d102 = true := by decide +kernel

private abbrev d103 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 49
private theorem p103 : mobiusTreeCheck cg 1200001 1 35904 d103 = true := by decide +kernel

private def d101 : MobiusCertTree := .branch d102 d103
private abbrev d105 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 50
private theorem p105 : mobiusTreeCheck cg 1200001 1 35968 d105 = true := by decide +kernel

private abbrev d106 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 51
private theorem p106 : mobiusTreeCheck cg 1200001 1 36032 d106 = true := by decide +kernel

private def d104 : MobiusCertTree := .branch d105 d106
private def d100 : MobiusCertTree := .branch d101 d104
private abbrev d109 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 52
private theorem p109 : mobiusTreeCheck cg 1200001 1 36096 d109 = true := by decide +kernel

private abbrev d110 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 53
private theorem p110 : mobiusTreeCheck cg 1200001 1 36160 d110 = true := by decide +kernel

private def d108 : MobiusCertTree := .branch d109 d110
private abbrev d112 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 54
private theorem p112 : mobiusTreeCheck cg 1200001 1 36224 d112 = true := by decide +kernel

private abbrev d113 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 55
private theorem p113 : mobiusTreeCheck cg 1200001 1 36288 d113 = true := by decide +kernel

private def d111 : MobiusCertTree := .branch d112 d113
private def d107 : MobiusCertTree := .branch d108 d111
private def d99 : MobiusCertTree := .branch d100 d107
private abbrev d117 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 56
private theorem p117 : mobiusTreeCheck cg 1200001 1 36352 d117 = true := by decide +kernel

private abbrev d118 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 57
private theorem p118 : mobiusTreeCheck cg 1200001 1 36416 d118 = true := by decide +kernel

private def d116 : MobiusCertTree := .branch d117 d118
private abbrev d120 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 58
private theorem p120 : mobiusTreeCheck cg 1200001 1 36480 d120 = true := by decide +kernel

private abbrev d121 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 59
private theorem p121 : mobiusTreeCheck cg 1200001 1 36544 d121 = true := by decide +kernel

private def d119 : MobiusCertTree := .branch d120 d121
private def d115 : MobiusCertTree := .branch d116 d119
private abbrev d124 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 60
private theorem p124 : mobiusTreeCheck cg 1200001 1 36608 d124 = true := by decide +kernel

private abbrev d125 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 61
private theorem p125 : mobiusTreeCheck cg 1200001 1 36672 d125 = true := by decide +kernel

private def d123 : MobiusCertTree := .branch d124 d125
private abbrev d127 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 62
private theorem p127 : mobiusTreeCheck cg 1200001 1 36736 d127 = true := by decide +kernel

private abbrev d128 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 63
private theorem p128 : mobiusTreeCheck cg 1200001 1 36800 d128 = true := by decide +kernel

private def d126 : MobiusCertTree := .branch d127 d128
private def d122 : MobiusCertTree := .branch d123 d126
private def d114 : MobiusCertTree := .branch d115 d122
private def d98 : MobiusCertTree := .branch d99 d114
private def d66 : MobiusCertTree := .branch d67 d98
private def d2 : MobiusCertTree := .branch d3 d66
private abbrev d135 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 64
private theorem p135 : mobiusTreeCheck cg 1200001 1 36864 d135 = true := by decide +kernel

private abbrev d136 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 65
private theorem p136 : mobiusTreeCheck cg 1200001 1 36928 d136 = true := by decide +kernel

private def d134 : MobiusCertTree := .branch d135 d136
private abbrev d138 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 66
private theorem p138 : mobiusTreeCheck cg 1200001 1 36992 d138 = true := by decide +kernel

private abbrev d139 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 67
private theorem p139 : mobiusTreeCheck cg 1200001 1 37056 d139 = true := by decide +kernel

private def d137 : MobiusCertTree := .branch d138 d139
private def d133 : MobiusCertTree := .branch d134 d137
private abbrev d142 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 68
private theorem p142 : mobiusTreeCheck cg 1200001 1 37120 d142 = true := by decide +kernel

private abbrev d143 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 69
private theorem p143 : mobiusTreeCheck cg 1200001 1 37184 d143 = true := by decide +kernel

private def d141 : MobiusCertTree := .branch d142 d143
private abbrev d145 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 70
private theorem p145 : mobiusTreeCheck cg 1200001 1 37248 d145 = true := by decide +kernel

private abbrev d146 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 71
private theorem p146 : mobiusTreeCheck cg 1200001 1 37312 d146 = true := by decide +kernel

private def d144 : MobiusCertTree := .branch d145 d146
private def d140 : MobiusCertTree := .branch d141 d144
private def d132 : MobiusCertTree := .branch d133 d140
private abbrev d150 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 72
private theorem p150 : mobiusTreeCheck cg 1200001 1 37376 d150 = true := by decide +kernel

private abbrev d151 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 73
private theorem p151 : mobiusTreeCheck cg 1200001 1 37440 d151 = true := by decide +kernel

private def d149 : MobiusCertTree := .branch d150 d151
private abbrev d153 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 74
private theorem p153 : mobiusTreeCheck cg 1200001 1 37504 d153 = true := by decide +kernel

private abbrev d154 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 75
private theorem p154 : mobiusTreeCheck cg 1200001 1 37568 d154 = true := by decide +kernel

private def d152 : MobiusCertTree := .branch d153 d154
private def d148 : MobiusCertTree := .branch d149 d152
private abbrev d157 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 76
private theorem p157 : mobiusTreeCheck cg 1200001 1 37632 d157 = true := by decide +kernel

private abbrev d158 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 77
private theorem p158 : mobiusTreeCheck cg 1200001 1 37696 d158 = true := by decide +kernel

private def d156 : MobiusCertTree := .branch d157 d158
private abbrev d160 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 78
private theorem p160 : mobiusTreeCheck cg 1200001 1 37760 d160 = true := by decide +kernel

private abbrev d161 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 79
private theorem p161 : mobiusTreeCheck cg 1200001 1 37824 d161 = true := by decide +kernel

private def d159 : MobiusCertTree := .branch d160 d161
private def d155 : MobiusCertTree := .branch d156 d159
private def d147 : MobiusCertTree := .branch d148 d155
private def d131 : MobiusCertTree := .branch d132 d147
private abbrev d166 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 80
private theorem p166 : mobiusTreeCheck cg 1200001 1 37888 d166 = true := by decide +kernel

private abbrev d167 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 81
private theorem p167 : mobiusTreeCheck cg 1200001 1 37952 d167 = true := by decide +kernel

private def d165 : MobiusCertTree := .branch d166 d167
private abbrev d169 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 82
private theorem p169 : mobiusTreeCheck cg 1200001 1 38016 d169 = true := by decide +kernel

private abbrev d170 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 83
private theorem p170 : mobiusTreeCheck cg 1200001 1 38080 d170 = true := by decide +kernel

private def d168 : MobiusCertTree := .branch d169 d170
private def d164 : MobiusCertTree := .branch d165 d168
private abbrev d173 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 84
private theorem p173 : mobiusTreeCheck cg 1200001 1 38144 d173 = true := by decide +kernel

private abbrev d174 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 85
private theorem p174 : mobiusTreeCheck cg 1200001 1 38208 d174 = true := by decide +kernel

private def d172 : MobiusCertTree := .branch d173 d174
private abbrev d176 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 86
private theorem p176 : mobiusTreeCheck cg 1200001 1 38272 d176 = true := by decide +kernel

private abbrev d177 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 87
private theorem p177 : mobiusTreeCheck cg 1200001 1 38336 d177 = true := by decide +kernel

private def d175 : MobiusCertTree := .branch d176 d177
private def d171 : MobiusCertTree := .branch d172 d175
private def d163 : MobiusCertTree := .branch d164 d171
private abbrev d181 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 88
private theorem p181 : mobiusTreeCheck cg 1200001 1 38400 d181 = true := by decide +kernel

private abbrev d182 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 89
private theorem p182 : mobiusTreeCheck cg 1200001 1 38464 d182 = true := by decide +kernel

private def d180 : MobiusCertTree := .branch d181 d182
private abbrev d184 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 90
private theorem p184 : mobiusTreeCheck cg 1200001 1 38528 d184 = true := by decide +kernel

private abbrev d185 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 91
private theorem p185 : mobiusTreeCheck cg 1200001 1 38592 d185 = true := by decide +kernel

private def d183 : MobiusCertTree := .branch d184 d185
private def d179 : MobiusCertTree := .branch d180 d183
private abbrev d188 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 92
private theorem p188 : mobiusTreeCheck cg 1200001 1 38656 d188 = true := by decide +kernel

private abbrev d189 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 93
private theorem p189 : mobiusTreeCheck cg 1200001 1 38720 d189 = true := by decide +kernel

private def d187 : MobiusCertTree := .branch d188 d189
private abbrev d191 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 94
private theorem p191 : mobiusTreeCheck cg 1200001 1 38784 d191 = true := by decide +kernel

private abbrev d192 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 95
private theorem p192 : mobiusTreeCheck cg 1200001 1 38848 d192 = true := by decide +kernel

private def d190 : MobiusCertTree := .branch d191 d192
private def d186 : MobiusCertTree := .branch d187 d190
private def d178 : MobiusCertTree := .branch d179 d186
private def d162 : MobiusCertTree := .branch d163 d178
private def d130 : MobiusCertTree := .branch d131 d162
private abbrev d198 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 96
private theorem p198 : mobiusTreeCheck cg 1200001 1 38912 d198 = true := by decide +kernel

private abbrev d199 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 97
private theorem p199 : mobiusTreeCheck cg 1200001 1 38976 d199 = true := by decide +kernel

private def d197 : MobiusCertTree := .branch d198 d199
private abbrev d201 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 98
private theorem p201 : mobiusTreeCheck cg 1200001 1 39040 d201 = true := by decide +kernel

private abbrev d202 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 99
private theorem p202 : mobiusTreeCheck cg 1200001 1 39104 d202 = true := by decide +kernel

private def d200 : MobiusCertTree := .branch d201 d202
private def d196 : MobiusCertTree := .branch d197 d200
private abbrev d205 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 100
private theorem p205 : mobiusTreeCheck cg 1200001 1 39168 d205 = true := by decide +kernel

private abbrev d206 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 101
private theorem p206 : mobiusTreeCheck cg 1200001 1 39232 d206 = true := by decide +kernel

private def d204 : MobiusCertTree := .branch d205 d206
private abbrev d208 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 102
private theorem p208 : mobiusTreeCheck cg 1200001 1 39296 d208 = true := by decide +kernel

private abbrev d209 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 103
private theorem p209 : mobiusTreeCheck cg 1200001 1 39360 d209 = true := by decide +kernel

private def d207 : MobiusCertTree := .branch d208 d209
private def d203 : MobiusCertTree := .branch d204 d207
private def d195 : MobiusCertTree := .branch d196 d203
private abbrev d213 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 104
private theorem p213 : mobiusTreeCheck cg 1200001 1 39424 d213 = true := by decide +kernel

private abbrev d214 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 105
private theorem p214 : mobiusTreeCheck cg 1200001 1 39488 d214 = true := by decide +kernel

private def d212 : MobiusCertTree := .branch d213 d214
private abbrev d216 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 106
private theorem p216 : mobiusTreeCheck cg 1200001 1 39552 d216 = true := by decide +kernel

private abbrev d217 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 107
private theorem p217 : mobiusTreeCheck cg 1200001 1 39616 d217 = true := by decide +kernel

private def d215 : MobiusCertTree := .branch d216 d217
private def d211 : MobiusCertTree := .branch d212 d215
private abbrev d220 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 108
private theorem p220 : mobiusTreeCheck cg 1200001 1 39680 d220 = true := by decide +kernel

private abbrev d221 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 109
private theorem p221 : mobiusTreeCheck cg 1200001 1 39744 d221 = true := by decide +kernel

private def d219 : MobiusCertTree := .branch d220 d221
private abbrev d223 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 110
private theorem p223 : mobiusTreeCheck cg 1200001 1 39808 d223 = true := by decide +kernel

private abbrev d224 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 111
private theorem p224 : mobiusTreeCheck cg 1200001 1 39872 d224 = true := by decide +kernel

private def d222 : MobiusCertTree := .branch d223 d224
private def d218 : MobiusCertTree := .branch d219 d222
private def d210 : MobiusCertTree := .branch d211 d218
private def d194 : MobiusCertTree := .branch d195 d210
private abbrev d229 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 112
private theorem p229 : mobiusTreeCheck cg 1200001 1 39936 d229 = true := by decide +kernel

private abbrev d230 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 113
private theorem p230 : mobiusTreeCheck cg 1200001 1 40000 d230 = true := by decide +kernel

private def d228 : MobiusCertTree := .branch d229 d230
private abbrev d232 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 114
private theorem p232 : mobiusTreeCheck cg 1200001 1 40064 d232 = true := by decide +kernel

private abbrev d233 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 115
private theorem p233 : mobiusTreeCheck cg 1200001 1 40128 d233 = true := by decide +kernel

private def d231 : MobiusCertTree := .branch d232 d233
private def d227 : MobiusCertTree := .branch d228 d231
private abbrev d236 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 116
private theorem p236 : mobiusTreeCheck cg 1200001 1 40192 d236 = true := by decide +kernel

private abbrev d237 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 117
private theorem p237 : mobiusTreeCheck cg 1200001 1 40256 d237 = true := by decide +kernel

private def d235 : MobiusCertTree := .branch d236 d237
private abbrev d239 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 118
private theorem p239 : mobiusTreeCheck cg 1200001 1 40320 d239 = true := by decide +kernel

private abbrev d240 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 119
private theorem p240 : mobiusTreeCheck cg 1200001 1 40384 d240 = true := by decide +kernel

private def d238 : MobiusCertTree := .branch d239 d240
private def d234 : MobiusCertTree := .branch d235 d238
private def d226 : MobiusCertTree := .branch d227 d234
private abbrev d244 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 120
private theorem p244 : mobiusTreeCheck cg 1200001 1 40448 d244 = true := by decide +kernel

private abbrev d245 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 121
private theorem p245 : mobiusTreeCheck cg 1200001 1 40512 d245 = true := by decide +kernel

private def d243 : MobiusCertTree := .branch d244 d245
private abbrev d247 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 122
private theorem p247 : mobiusTreeCheck cg 1200001 1 40576 d247 = true := by decide +kernel

private abbrev d248 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 123
private theorem p248 : mobiusTreeCheck cg 1200001 1 40640 d248 = true := by decide +kernel

private def d246 : MobiusCertTree := .branch d247 d248
private def d242 : MobiusCertTree := .branch d243 d246
private abbrev d251 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 124
private theorem p251 : mobiusTreeCheck cg 1200001 1 40704 d251 = true := by decide +kernel

private abbrev d252 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 125
private theorem p252 : mobiusTreeCheck cg 1200001 1 40768 d252 = true := by decide +kernel

private def d250 : MobiusCertTree := .branch d251 d252
private abbrev d254 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 126
private theorem p254 : mobiusTreeCheck cg 1200001 1 40832 d254 = true := by decide +kernel

private abbrev d255 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock004 127
private theorem p255 : mobiusTreeCheck cg 1200001 1 40896 d255 = true := by decide +kernel

private def d253 : MobiusCertTree := .branch d254 d255
private def d249 : MobiusCertTree := .branch d250 d253
private def d241 : MobiusCertTree := .branch d242 d249
private def d225 : MobiusCertTree := .branch d226 d241
private def d193 : MobiusCertTree := .branch d194 d225
private def d129 : MobiusCertTree := .branch d130 d193
private def d1 : MobiusCertTree := .branch d2 d129
private abbrev d263 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 0
private theorem p263 : mobiusTreeCheck cg 1200001 1 40960 d263 = true := by decide +kernel

private abbrev d264 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 1
private theorem p264 : mobiusTreeCheck cg 1200001 1 41024 d264 = true := by decide +kernel

private def d262 : MobiusCertTree := .branch d263 d264
private abbrev d266 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 2
private theorem p266 : mobiusTreeCheck cg 1200001 1 41088 d266 = true := by decide +kernel

private abbrev d267 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 3
private theorem p267 : mobiusTreeCheck cg 1200001 1 41152 d267 = true := by decide +kernel

private def d265 : MobiusCertTree := .branch d266 d267
private def d261 : MobiusCertTree := .branch d262 d265
private abbrev d270 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 4
private theorem p270 : mobiusTreeCheck cg 1200001 1 41216 d270 = true := by decide +kernel

private abbrev d271 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 5
private theorem p271 : mobiusTreeCheck cg 1200001 1 41280 d271 = true := by decide +kernel

private def d269 : MobiusCertTree := .branch d270 d271
private abbrev d273 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 6
private theorem p273 : mobiusTreeCheck cg 1200001 1 41344 d273 = true := by decide +kernel

private abbrev d274 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 7
private theorem p274 : mobiusTreeCheck cg 1200001 1 41408 d274 = true := by decide +kernel

private def d272 : MobiusCertTree := .branch d273 d274
private def d268 : MobiusCertTree := .branch d269 d272
private def d260 : MobiusCertTree := .branch d261 d268
private abbrev d278 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 8
private theorem p278 : mobiusTreeCheck cg 1200001 1 41472 d278 = true := by decide +kernel

private abbrev d279 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 9
private theorem p279 : mobiusTreeCheck cg 1200001 1 41536 d279 = true := by decide +kernel

private def d277 : MobiusCertTree := .branch d278 d279
private abbrev d281 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 10
private theorem p281 : mobiusTreeCheck cg 1200001 1 41600 d281 = true := by decide +kernel

private abbrev d282 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 11
private theorem p282 : mobiusTreeCheck cg 1200001 1 41664 d282 = true := by decide +kernel

private def d280 : MobiusCertTree := .branch d281 d282
private def d276 : MobiusCertTree := .branch d277 d280
private abbrev d285 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 12
private theorem p285 : mobiusTreeCheck cg 1200001 1 41728 d285 = true := by decide +kernel

private abbrev d286 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 13
private theorem p286 : mobiusTreeCheck cg 1200001 1 41792 d286 = true := by decide +kernel

private def d284 : MobiusCertTree := .branch d285 d286
private abbrev d288 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 14
private theorem p288 : mobiusTreeCheck cg 1200001 1 41856 d288 = true := by decide +kernel

private abbrev d289 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 15
private theorem p289 : mobiusTreeCheck cg 1200001 1 41920 d289 = true := by decide +kernel

private def d287 : MobiusCertTree := .branch d288 d289
private def d283 : MobiusCertTree := .branch d284 d287
private def d275 : MobiusCertTree := .branch d276 d283
private def d259 : MobiusCertTree := .branch d260 d275
private abbrev d294 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 16
private theorem p294 : mobiusTreeCheck cg 1200001 1 41984 d294 = true := by decide +kernel

private abbrev d295 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 17
private theorem p295 : mobiusTreeCheck cg 1200001 1 42048 d295 = true := by decide +kernel

private def d293 : MobiusCertTree := .branch d294 d295
private abbrev d297 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 18
private theorem p297 : mobiusTreeCheck cg 1200001 1 42112 d297 = true := by decide +kernel

private abbrev d298 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 19
private theorem p298 : mobiusTreeCheck cg 1200001 1 42176 d298 = true := by decide +kernel

private def d296 : MobiusCertTree := .branch d297 d298
private def d292 : MobiusCertTree := .branch d293 d296
private abbrev d301 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 20
private theorem p301 : mobiusTreeCheck cg 1200001 1 42240 d301 = true := by decide +kernel

private abbrev d302 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 21
private theorem p302 : mobiusTreeCheck cg 1200001 1 42304 d302 = true := by decide +kernel

private def d300 : MobiusCertTree := .branch d301 d302
private abbrev d304 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 22
private theorem p304 : mobiusTreeCheck cg 1200001 1 42368 d304 = true := by decide +kernel

private abbrev d305 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 23
private theorem p305 : mobiusTreeCheck cg 1200001 1 42432 d305 = true := by decide +kernel

private def d303 : MobiusCertTree := .branch d304 d305
private def d299 : MobiusCertTree := .branch d300 d303
private def d291 : MobiusCertTree := .branch d292 d299
private abbrev d309 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 24
private theorem p309 : mobiusTreeCheck cg 1200001 1 42496 d309 = true := by decide +kernel

private abbrev d310 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 25
private theorem p310 : mobiusTreeCheck cg 1200001 1 42560 d310 = true := by decide +kernel

private def d308 : MobiusCertTree := .branch d309 d310
private abbrev d312 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 26
private theorem p312 : mobiusTreeCheck cg 1200001 1 42624 d312 = true := by decide +kernel

private abbrev d313 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 27
private theorem p313 : mobiusTreeCheck cg 1200001 1 42688 d313 = true := by decide +kernel

private def d311 : MobiusCertTree := .branch d312 d313
private def d307 : MobiusCertTree := .branch d308 d311
private abbrev d316 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 28
private theorem p316 : mobiusTreeCheck cg 1200001 1 42752 d316 = true := by decide +kernel

private abbrev d317 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 29
private theorem p317 : mobiusTreeCheck cg 1200001 1 42816 d317 = true := by decide +kernel

private def d315 : MobiusCertTree := .branch d316 d317
private abbrev d319 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 30
private theorem p319 : mobiusTreeCheck cg 1200001 1 42880 d319 = true := by decide +kernel

private abbrev d320 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 31
private theorem p320 : mobiusTreeCheck cg 1200001 1 42944 d320 = true := by decide +kernel

private def d318 : MobiusCertTree := .branch d319 d320
private def d314 : MobiusCertTree := .branch d315 d318
private def d306 : MobiusCertTree := .branch d307 d314
private def d290 : MobiusCertTree := .branch d291 d306
private def d258 : MobiusCertTree := .branch d259 d290
private abbrev d326 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 32
private theorem p326 : mobiusTreeCheck cg 1200001 1 43008 d326 = true := by decide +kernel

private abbrev d327 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 33
private theorem p327 : mobiusTreeCheck cg 1200001 1 43072 d327 = true := by decide +kernel

private def d325 : MobiusCertTree := .branch d326 d327
private abbrev d329 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 34
private theorem p329 : mobiusTreeCheck cg 1200001 1 43136 d329 = true := by decide +kernel

private abbrev d330 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 35
private theorem p330 : mobiusTreeCheck cg 1200001 1 43200 d330 = true := by decide +kernel

private def d328 : MobiusCertTree := .branch d329 d330
private def d324 : MobiusCertTree := .branch d325 d328
private abbrev d333 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 36
private theorem p333 : mobiusTreeCheck cg 1200001 1 43264 d333 = true := by decide +kernel

private abbrev d334 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 37
private theorem p334 : mobiusTreeCheck cg 1200001 1 43328 d334 = true := by decide +kernel

private def d332 : MobiusCertTree := .branch d333 d334
private abbrev d336 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 38
private theorem p336 : mobiusTreeCheck cg 1200001 1 43392 d336 = true := by decide +kernel

private abbrev d337 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 39
private theorem p337 : mobiusTreeCheck cg 1200001 1 43456 d337 = true := by decide +kernel

private def d335 : MobiusCertTree := .branch d336 d337
private def d331 : MobiusCertTree := .branch d332 d335
private def d323 : MobiusCertTree := .branch d324 d331
private abbrev d341 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 40
private theorem p341 : mobiusTreeCheck cg 1200001 1 43520 d341 = true := by decide +kernel

private abbrev d342 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 41
private theorem p342 : mobiusTreeCheck cg 1200001 1 43584 d342 = true := by decide +kernel

private def d340 : MobiusCertTree := .branch d341 d342
private abbrev d344 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 42
private theorem p344 : mobiusTreeCheck cg 1200001 1 43648 d344 = true := by decide +kernel

private abbrev d345 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 43
private theorem p345 : mobiusTreeCheck cg 1200001 1 43712 d345 = true := by decide +kernel

private def d343 : MobiusCertTree := .branch d344 d345
private def d339 : MobiusCertTree := .branch d340 d343
private abbrev d348 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 44
private theorem p348 : mobiusTreeCheck cg 1200001 1 43776 d348 = true := by decide +kernel

private abbrev d349 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 45
private theorem p349 : mobiusTreeCheck cg 1200001 1 43840 d349 = true := by decide +kernel

private def d347 : MobiusCertTree := .branch d348 d349
private abbrev d351 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 46
private theorem p351 : mobiusTreeCheck cg 1200001 1 43904 d351 = true := by decide +kernel

private abbrev d352 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 47
private theorem p352 : mobiusTreeCheck cg 1200001 1 43968 d352 = true := by decide +kernel

private def d350 : MobiusCertTree := .branch d351 d352
private def d346 : MobiusCertTree := .branch d347 d350
private def d338 : MobiusCertTree := .branch d339 d346
private def d322 : MobiusCertTree := .branch d323 d338
private abbrev d357 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 48
private theorem p357 : mobiusTreeCheck cg 1200001 1 44032 d357 = true := by decide +kernel

private abbrev d358 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 49
private theorem p358 : mobiusTreeCheck cg 1200001 1 44096 d358 = true := by decide +kernel

private def d356 : MobiusCertTree := .branch d357 d358
private abbrev d360 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 50
private theorem p360 : mobiusTreeCheck cg 1200001 1 44160 d360 = true := by decide +kernel

private abbrev d361 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 51
private theorem p361 : mobiusTreeCheck cg 1200001 1 44224 d361 = true := by decide +kernel

private def d359 : MobiusCertTree := .branch d360 d361
private def d355 : MobiusCertTree := .branch d356 d359
private abbrev d364 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 52
private theorem p364 : mobiusTreeCheck cg 1200001 1 44288 d364 = true := by decide +kernel

private abbrev d365 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 53
private theorem p365 : mobiusTreeCheck cg 1200001 1 44352 d365 = true := by decide +kernel

private def d363 : MobiusCertTree := .branch d364 d365
private abbrev d367 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 54
private theorem p367 : mobiusTreeCheck cg 1200001 1 44416 d367 = true := by decide +kernel

private abbrev d368 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 55
private theorem p368 : mobiusTreeCheck cg 1200001 1 44480 d368 = true := by decide +kernel

private def d366 : MobiusCertTree := .branch d367 d368
private def d362 : MobiusCertTree := .branch d363 d366
private def d354 : MobiusCertTree := .branch d355 d362
private abbrev d372 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 56
private theorem p372 : mobiusTreeCheck cg 1200001 1 44544 d372 = true := by decide +kernel

private abbrev d373 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 57
private theorem p373 : mobiusTreeCheck cg 1200001 1 44608 d373 = true := by decide +kernel

private def d371 : MobiusCertTree := .branch d372 d373
private abbrev d375 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 58
private theorem p375 : mobiusTreeCheck cg 1200001 1 44672 d375 = true := by decide +kernel

private abbrev d376 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 59
private theorem p376 : mobiusTreeCheck cg 1200001 1 44736 d376 = true := by decide +kernel

private def d374 : MobiusCertTree := .branch d375 d376
private def d370 : MobiusCertTree := .branch d371 d374
private abbrev d379 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 60
private theorem p379 : mobiusTreeCheck cg 1200001 1 44800 d379 = true := by decide +kernel

private abbrev d380 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 61
private theorem p380 : mobiusTreeCheck cg 1200001 1 44864 d380 = true := by decide +kernel

private def d378 : MobiusCertTree := .branch d379 d380
private abbrev d382 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 62
private theorem p382 : mobiusTreeCheck cg 1200001 1 44928 d382 = true := by decide +kernel

private abbrev d383 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 63
private theorem p383 : mobiusTreeCheck cg 1200001 1 44992 d383 = true := by decide +kernel

private def d381 : MobiusCertTree := .branch d382 d383
private def d377 : MobiusCertTree := .branch d378 d381
private def d369 : MobiusCertTree := .branch d370 d377
private def d353 : MobiusCertTree := .branch d354 d369
private def d321 : MobiusCertTree := .branch d322 d353
private def d257 : MobiusCertTree := .branch d258 d321
private abbrev d390 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 64
private theorem p390 : mobiusTreeCheck cg 1200001 1 45056 d390 = true := by decide +kernel

private abbrev d391 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 65
private theorem p391 : mobiusTreeCheck cg 1200001 1 45120 d391 = true := by decide +kernel

private def d389 : MobiusCertTree := .branch d390 d391
private abbrev d393 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 66
private theorem p393 : mobiusTreeCheck cg 1200001 1 45184 d393 = true := by decide +kernel

private abbrev d394 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 67
private theorem p394 : mobiusTreeCheck cg 1200001 1 45248 d394 = true := by decide +kernel

private def d392 : MobiusCertTree := .branch d393 d394
private def d388 : MobiusCertTree := .branch d389 d392
private abbrev d397 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 68
private theorem p397 : mobiusTreeCheck cg 1200001 1 45312 d397 = true := by decide +kernel

private abbrev d398 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 69
private theorem p398 : mobiusTreeCheck cg 1200001 1 45376 d398 = true := by decide +kernel

private def d396 : MobiusCertTree := .branch d397 d398
private abbrev d400 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 70
private theorem p400 : mobiusTreeCheck cg 1200001 1 45440 d400 = true := by decide +kernel

private abbrev d401 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 71
private theorem p401 : mobiusTreeCheck cg 1200001 1 45504 d401 = true := by decide +kernel

private def d399 : MobiusCertTree := .branch d400 d401
private def d395 : MobiusCertTree := .branch d396 d399
private def d387 : MobiusCertTree := .branch d388 d395
private abbrev d405 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 72
private theorem p405 : mobiusTreeCheck cg 1200001 1 45568 d405 = true := by decide +kernel

private abbrev d406 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 73
private theorem p406 : mobiusTreeCheck cg 1200001 1 45632 d406 = true := by decide +kernel

private def d404 : MobiusCertTree := .branch d405 d406
private abbrev d408 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 74
private theorem p408 : mobiusTreeCheck cg 1200001 1 45696 d408 = true := by decide +kernel

private abbrev d409 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 75
private theorem p409 : mobiusTreeCheck cg 1200001 1 45760 d409 = true := by decide +kernel

private def d407 : MobiusCertTree := .branch d408 d409
private def d403 : MobiusCertTree := .branch d404 d407
private abbrev d412 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 76
private theorem p412 : mobiusTreeCheck cg 1200001 1 45824 d412 = true := by decide +kernel

private abbrev d413 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 77
private theorem p413 : mobiusTreeCheck cg 1200001 1 45888 d413 = true := by decide +kernel

private def d411 : MobiusCertTree := .branch d412 d413
private abbrev d415 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 78
private theorem p415 : mobiusTreeCheck cg 1200001 1 45952 d415 = true := by decide +kernel

private abbrev d416 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 79
private theorem p416 : mobiusTreeCheck cg 1200001 1 46016 d416 = true := by decide +kernel

private def d414 : MobiusCertTree := .branch d415 d416
private def d410 : MobiusCertTree := .branch d411 d414
private def d402 : MobiusCertTree := .branch d403 d410
private def d386 : MobiusCertTree := .branch d387 d402
private abbrev d421 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 80
private theorem p421 : mobiusTreeCheck cg 1200001 1 46080 d421 = true := by decide +kernel

private abbrev d422 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 81
private theorem p422 : mobiusTreeCheck cg 1200001 1 46144 d422 = true := by decide +kernel

private def d420 : MobiusCertTree := .branch d421 d422
private abbrev d424 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 82
private theorem p424 : mobiusTreeCheck cg 1200001 1 46208 d424 = true := by decide +kernel

private abbrev d425 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 83
private theorem p425 : mobiusTreeCheck cg 1200001 1 46272 d425 = true := by decide +kernel

private def d423 : MobiusCertTree := .branch d424 d425
private def d419 : MobiusCertTree := .branch d420 d423
private abbrev d428 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 84
private theorem p428 : mobiusTreeCheck cg 1200001 1 46336 d428 = true := by decide +kernel

private abbrev d429 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 85
private theorem p429 : mobiusTreeCheck cg 1200001 1 46400 d429 = true := by decide +kernel

private def d427 : MobiusCertTree := .branch d428 d429
private abbrev d431 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 86
private theorem p431 : mobiusTreeCheck cg 1200001 1 46464 d431 = true := by decide +kernel

private abbrev d432 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 87
private theorem p432 : mobiusTreeCheck cg 1200001 1 46528 d432 = true := by decide +kernel

private def d430 : MobiusCertTree := .branch d431 d432
private def d426 : MobiusCertTree := .branch d427 d430
private def d418 : MobiusCertTree := .branch d419 d426
private abbrev d436 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 88
private theorem p436 : mobiusTreeCheck cg 1200001 1 46592 d436 = true := by decide +kernel

private abbrev d437 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 89
private theorem p437 : mobiusTreeCheck cg 1200001 1 46656 d437 = true := by decide +kernel

private def d435 : MobiusCertTree := .branch d436 d437
private abbrev d439 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 90
private theorem p439 : mobiusTreeCheck cg 1200001 1 46720 d439 = true := by decide +kernel

private abbrev d440 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 91
private theorem p440 : mobiusTreeCheck cg 1200001 1 46784 d440 = true := by decide +kernel

private def d438 : MobiusCertTree := .branch d439 d440
private def d434 : MobiusCertTree := .branch d435 d438
private abbrev d443 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 92
private theorem p443 : mobiusTreeCheck cg 1200001 1 46848 d443 = true := by decide +kernel

private abbrev d444 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 93
private theorem p444 : mobiusTreeCheck cg 1200001 1 46912 d444 = true := by decide +kernel

private def d442 : MobiusCertTree := .branch d443 d444
private abbrev d446 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 94
private theorem p446 : mobiusTreeCheck cg 1200001 1 46976 d446 = true := by decide +kernel

private abbrev d447 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 95
private theorem p447 : mobiusTreeCheck cg 1200001 1 47040 d447 = true := by decide +kernel

private def d445 : MobiusCertTree := .branch d446 d447
private def d441 : MobiusCertTree := .branch d442 d445
private def d433 : MobiusCertTree := .branch d434 d441
private def d417 : MobiusCertTree := .branch d418 d433
private def d385 : MobiusCertTree := .branch d386 d417
private abbrev d453 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 96
private theorem p453 : mobiusTreeCheck cg 1200001 1 47104 d453 = true := by decide +kernel

private abbrev d454 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 97
private theorem p454 : mobiusTreeCheck cg 1200001 1 47168 d454 = true := by decide +kernel

private def d452 : MobiusCertTree := .branch d453 d454
private abbrev d456 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 98
private theorem p456 : mobiusTreeCheck cg 1200001 1 47232 d456 = true := by decide +kernel

private abbrev d457 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 99
private theorem p457 : mobiusTreeCheck cg 1200001 1 47296 d457 = true := by decide +kernel

private def d455 : MobiusCertTree := .branch d456 d457
private def d451 : MobiusCertTree := .branch d452 d455
private abbrev d460 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 100
private theorem p460 : mobiusTreeCheck cg 1200001 1 47360 d460 = true := by decide +kernel

private abbrev d461 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 101
private theorem p461 : mobiusTreeCheck cg 1200001 1 47424 d461 = true := by decide +kernel

private def d459 : MobiusCertTree := .branch d460 d461
private abbrev d463 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 102
private theorem p463 : mobiusTreeCheck cg 1200001 1 47488 d463 = true := by decide +kernel

private abbrev d464 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 103
private theorem p464 : mobiusTreeCheck cg 1200001 1 47552 d464 = true := by decide +kernel

private def d462 : MobiusCertTree := .branch d463 d464
private def d458 : MobiusCertTree := .branch d459 d462
private def d450 : MobiusCertTree := .branch d451 d458
private abbrev d468 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 104
private theorem p468 : mobiusTreeCheck cg 1200001 1 47616 d468 = true := by decide +kernel

private abbrev d469 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 105
private theorem p469 : mobiusTreeCheck cg 1200001 1 47680 d469 = true := by decide +kernel

private def d467 : MobiusCertTree := .branch d468 d469
private abbrev d471 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 106
private theorem p471 : mobiusTreeCheck cg 1200001 1 47744 d471 = true := by decide +kernel

private abbrev d472 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 107
private theorem p472 : mobiusTreeCheck cg 1200001 1 47808 d472 = true := by decide +kernel

private def d470 : MobiusCertTree := .branch d471 d472
private def d466 : MobiusCertTree := .branch d467 d470
private abbrev d475 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 108
private theorem p475 : mobiusTreeCheck cg 1200001 1 47872 d475 = true := by decide +kernel

private abbrev d476 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 109
private theorem p476 : mobiusTreeCheck cg 1200001 1 47936 d476 = true := by decide +kernel

private def d474 : MobiusCertTree := .branch d475 d476
private abbrev d478 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 110
private theorem p478 : mobiusTreeCheck cg 1200001 1 48000 d478 = true := by decide +kernel

private abbrev d479 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 111
private theorem p479 : mobiusTreeCheck cg 1200001 1 48064 d479 = true := by decide +kernel

private def d477 : MobiusCertTree := .branch d478 d479
private def d473 : MobiusCertTree := .branch d474 d477
private def d465 : MobiusCertTree := .branch d466 d473
private def d449 : MobiusCertTree := .branch d450 d465
private abbrev d484 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 112
private theorem p484 : mobiusTreeCheck cg 1200001 1 48128 d484 = true := by decide +kernel

private abbrev d485 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 113
private theorem p485 : mobiusTreeCheck cg 1200001 1 48192 d485 = true := by decide +kernel

private def d483 : MobiusCertTree := .branch d484 d485
private abbrev d487 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 114
private theorem p487 : mobiusTreeCheck cg 1200001 1 48256 d487 = true := by decide +kernel

private abbrev d488 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 115
private theorem p488 : mobiusTreeCheck cg 1200001 1 48320 d488 = true := by decide +kernel

private def d486 : MobiusCertTree := .branch d487 d488
private def d482 : MobiusCertTree := .branch d483 d486
private abbrev d491 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 116
private theorem p491 : mobiusTreeCheck cg 1200001 1 48384 d491 = true := by decide +kernel

private abbrev d492 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 117
private theorem p492 : mobiusTreeCheck cg 1200001 1 48448 d492 = true := by decide +kernel

private def d490 : MobiusCertTree := .branch d491 d492
private abbrev d494 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 118
private theorem p494 : mobiusTreeCheck cg 1200001 1 48512 d494 = true := by decide +kernel

private abbrev d495 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 119
private theorem p495 : mobiusTreeCheck cg 1200001 1 48576 d495 = true := by decide +kernel

private def d493 : MobiusCertTree := .branch d494 d495
private def d489 : MobiusCertTree := .branch d490 d493
private def d481 : MobiusCertTree := .branch d482 d489
private abbrev d499 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 120
private theorem p499 : mobiusTreeCheck cg 1200001 1 48640 d499 = true := by decide +kernel

private abbrev d500 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 121
private theorem p500 : mobiusTreeCheck cg 1200001 1 48704 d500 = true := by decide +kernel

private def d498 : MobiusCertTree := .branch d499 d500
private abbrev d502 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 122
private theorem p502 : mobiusTreeCheck cg 1200001 1 48768 d502 = true := by decide +kernel

private abbrev d503 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 123
private theorem p503 : mobiusTreeCheck cg 1200001 1 48832 d503 = true := by decide +kernel

private def d501 : MobiusCertTree := .branch d502 d503
private def d497 : MobiusCertTree := .branch d498 d501
private abbrev d506 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 124
private theorem p506 : mobiusTreeCheck cg 1200001 1 48896 d506 = true := by decide +kernel

private abbrev d507 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 125
private theorem p507 : mobiusTreeCheck cg 1200001 1 48960 d507 = true := by decide +kernel

private def d505 : MobiusCertTree := .branch d506 d507
private abbrev d509 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 126
private theorem p509 : mobiusTreeCheck cg 1200001 1 49024 d509 = true := by decide +kernel

private abbrev d510 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock005 127
private theorem p510 : mobiusTreeCheck cg 1200001 1 49088 d510 = true := by decide +kernel

private def d508 : MobiusCertTree := .branch d509 d510
private def d504 : MobiusCertTree := .branch d505 d508
private def d496 : MobiusCertTree := .branch d497 d504
private def d480 : MobiusCertTree := .branch d481 d496
private def d448 : MobiusCertTree := .branch d449 d480
private def d384 : MobiusCertTree := .branch d385 d448
private def d256 : MobiusCertTree := .branch d257 d384
private def d0 : MobiusCertTree := .branch d1 d256

private theorem combined : mobiusTreeCheck cg 1200001 9 32768 d0 = true :=
  (mobiusTreeCheck_join cg 1200001 8 32768 _ _ (mobiusTreeCheck_join cg 1200001 7 32768 _ _ (mobiusTreeCheck_join cg 1200001 6 32768 _ _ (mobiusTreeCheck_join cg 1200001 5 32768 _ _ (mobiusTreeCheck_join cg 1200001 4 32768 _ _ (mobiusTreeCheck_join cg 1200001 3 32768 _ _ (mobiusTreeCheck_join cg 1200001 2 32768 _ _ (mobiusTreeCheck_join cg 1200001 1 32768 _ _ p8 p9) (mobiusTreeCheck_join cg 1200001 1 32896 _ _ p11 p12)) (mobiusTreeCheck_join cg 1200001 2 33024 _ _ (mobiusTreeCheck_join cg 1200001 1 33024 _ _ p15 p16) (mobiusTreeCheck_join cg 1200001 1 33152 _ _ p18 p19))) (mobiusTreeCheck_join cg 1200001 3 33280 _ _ (mobiusTreeCheck_join cg 1200001 2 33280 _ _ (mobiusTreeCheck_join cg 1200001 1 33280 _ _ p23 p24) (mobiusTreeCheck_join cg 1200001 1 33408 _ _ p26 p27)) (mobiusTreeCheck_join cg 1200001 2 33536 _ _ (mobiusTreeCheck_join cg 1200001 1 33536 _ _ p30 p31) (mobiusTreeCheck_join cg 1200001 1 33664 _ _ p33 p34)))) (mobiusTreeCheck_join cg 1200001 4 33792 _ _ (mobiusTreeCheck_join cg 1200001 3 33792 _ _ (mobiusTreeCheck_join cg 1200001 2 33792 _ _ (mobiusTreeCheck_join cg 1200001 1 33792 _ _ p39 p40) (mobiusTreeCheck_join cg 1200001 1 33920 _ _ p42 p43)) (mobiusTreeCheck_join cg 1200001 2 34048 _ _ (mobiusTreeCheck_join cg 1200001 1 34048 _ _ p46 p47) (mobiusTreeCheck_join cg 1200001 1 34176 _ _ p49 p50))) (mobiusTreeCheck_join cg 1200001 3 34304 _ _ (mobiusTreeCheck_join cg 1200001 2 34304 _ _ (mobiusTreeCheck_join cg 1200001 1 34304 _ _ p54 p55) (mobiusTreeCheck_join cg 1200001 1 34432 _ _ p57 p58)) (mobiusTreeCheck_join cg 1200001 2 34560 _ _ (mobiusTreeCheck_join cg 1200001 1 34560 _ _ p61 p62) (mobiusTreeCheck_join cg 1200001 1 34688 _ _ p64 p65))))) (mobiusTreeCheck_join cg 1200001 5 34816 _ _ (mobiusTreeCheck_join cg 1200001 4 34816 _ _ (mobiusTreeCheck_join cg 1200001 3 34816 _ _ (mobiusTreeCheck_join cg 1200001 2 34816 _ _ (mobiusTreeCheck_join cg 1200001 1 34816 _ _ p71 p72) (mobiusTreeCheck_join cg 1200001 1 34944 _ _ p74 p75)) (mobiusTreeCheck_join cg 1200001 2 35072 _ _ (mobiusTreeCheck_join cg 1200001 1 35072 _ _ p78 p79) (mobiusTreeCheck_join cg 1200001 1 35200 _ _ p81 p82))) (mobiusTreeCheck_join cg 1200001 3 35328 _ _ (mobiusTreeCheck_join cg 1200001 2 35328 _ _ (mobiusTreeCheck_join cg 1200001 1 35328 _ _ p86 p87) (mobiusTreeCheck_join cg 1200001 1 35456 _ _ p89 p90)) (mobiusTreeCheck_join cg 1200001 2 35584 _ _ (mobiusTreeCheck_join cg 1200001 1 35584 _ _ p93 p94) (mobiusTreeCheck_join cg 1200001 1 35712 _ _ p96 p97)))) (mobiusTreeCheck_join cg 1200001 4 35840 _ _ (mobiusTreeCheck_join cg 1200001 3 35840 _ _ (mobiusTreeCheck_join cg 1200001 2 35840 _ _ (mobiusTreeCheck_join cg 1200001 1 35840 _ _ p102 p103) (mobiusTreeCheck_join cg 1200001 1 35968 _ _ p105 p106)) (mobiusTreeCheck_join cg 1200001 2 36096 _ _ (mobiusTreeCheck_join cg 1200001 1 36096 _ _ p109 p110) (mobiusTreeCheck_join cg 1200001 1 36224 _ _ p112 p113))) (mobiusTreeCheck_join cg 1200001 3 36352 _ _ (mobiusTreeCheck_join cg 1200001 2 36352 _ _ (mobiusTreeCheck_join cg 1200001 1 36352 _ _ p117 p118) (mobiusTreeCheck_join cg 1200001 1 36480 _ _ p120 p121)) (mobiusTreeCheck_join cg 1200001 2 36608 _ _ (mobiusTreeCheck_join cg 1200001 1 36608 _ _ p124 p125) (mobiusTreeCheck_join cg 1200001 1 36736 _ _ p127 p128)))))) (mobiusTreeCheck_join cg 1200001 6 36864 _ _ (mobiusTreeCheck_join cg 1200001 5 36864 _ _ (mobiusTreeCheck_join cg 1200001 4 36864 _ _ (mobiusTreeCheck_join cg 1200001 3 36864 _ _ (mobiusTreeCheck_join cg 1200001 2 36864 _ _ (mobiusTreeCheck_join cg 1200001 1 36864 _ _ p135 p136) (mobiusTreeCheck_join cg 1200001 1 36992 _ _ p138 p139)) (mobiusTreeCheck_join cg 1200001 2 37120 _ _ (mobiusTreeCheck_join cg 1200001 1 37120 _ _ p142 p143) (mobiusTreeCheck_join cg 1200001 1 37248 _ _ p145 p146))) (mobiusTreeCheck_join cg 1200001 3 37376 _ _ (mobiusTreeCheck_join cg 1200001 2 37376 _ _ (mobiusTreeCheck_join cg 1200001 1 37376 _ _ p150 p151) (mobiusTreeCheck_join cg 1200001 1 37504 _ _ p153 p154)) (mobiusTreeCheck_join cg 1200001 2 37632 _ _ (mobiusTreeCheck_join cg 1200001 1 37632 _ _ p157 p158) (mobiusTreeCheck_join cg 1200001 1 37760 _ _ p160 p161)))) (mobiusTreeCheck_join cg 1200001 4 37888 _ _ (mobiusTreeCheck_join cg 1200001 3 37888 _ _ (mobiusTreeCheck_join cg 1200001 2 37888 _ _ (mobiusTreeCheck_join cg 1200001 1 37888 _ _ p166 p167) (mobiusTreeCheck_join cg 1200001 1 38016 _ _ p169 p170)) (mobiusTreeCheck_join cg 1200001 2 38144 _ _ (mobiusTreeCheck_join cg 1200001 1 38144 _ _ p173 p174) (mobiusTreeCheck_join cg 1200001 1 38272 _ _ p176 p177))) (mobiusTreeCheck_join cg 1200001 3 38400 _ _ (mobiusTreeCheck_join cg 1200001 2 38400 _ _ (mobiusTreeCheck_join cg 1200001 1 38400 _ _ p181 p182) (mobiusTreeCheck_join cg 1200001 1 38528 _ _ p184 p185)) (mobiusTreeCheck_join cg 1200001 2 38656 _ _ (mobiusTreeCheck_join cg 1200001 1 38656 _ _ p188 p189) (mobiusTreeCheck_join cg 1200001 1 38784 _ _ p191 p192))))) (mobiusTreeCheck_join cg 1200001 5 38912 _ _ (mobiusTreeCheck_join cg 1200001 4 38912 _ _ (mobiusTreeCheck_join cg 1200001 3 38912 _ _ (mobiusTreeCheck_join cg 1200001 2 38912 _ _ (mobiusTreeCheck_join cg 1200001 1 38912 _ _ p198 p199) (mobiusTreeCheck_join cg 1200001 1 39040 _ _ p201 p202)) (mobiusTreeCheck_join cg 1200001 2 39168 _ _ (mobiusTreeCheck_join cg 1200001 1 39168 _ _ p205 p206) (mobiusTreeCheck_join cg 1200001 1 39296 _ _ p208 p209))) (mobiusTreeCheck_join cg 1200001 3 39424 _ _ (mobiusTreeCheck_join cg 1200001 2 39424 _ _ (mobiusTreeCheck_join cg 1200001 1 39424 _ _ p213 p214) (mobiusTreeCheck_join cg 1200001 1 39552 _ _ p216 p217)) (mobiusTreeCheck_join cg 1200001 2 39680 _ _ (mobiusTreeCheck_join cg 1200001 1 39680 _ _ p220 p221) (mobiusTreeCheck_join cg 1200001 1 39808 _ _ p223 p224)))) (mobiusTreeCheck_join cg 1200001 4 39936 _ _ (mobiusTreeCheck_join cg 1200001 3 39936 _ _ (mobiusTreeCheck_join cg 1200001 2 39936 _ _ (mobiusTreeCheck_join cg 1200001 1 39936 _ _ p229 p230) (mobiusTreeCheck_join cg 1200001 1 40064 _ _ p232 p233)) (mobiusTreeCheck_join cg 1200001 2 40192 _ _ (mobiusTreeCheck_join cg 1200001 1 40192 _ _ p236 p237) (mobiusTreeCheck_join cg 1200001 1 40320 _ _ p239 p240))) (mobiusTreeCheck_join cg 1200001 3 40448 _ _ (mobiusTreeCheck_join cg 1200001 2 40448 _ _ (mobiusTreeCheck_join cg 1200001 1 40448 _ _ p244 p245) (mobiusTreeCheck_join cg 1200001 1 40576 _ _ p247 p248)) (mobiusTreeCheck_join cg 1200001 2 40704 _ _ (mobiusTreeCheck_join cg 1200001 1 40704 _ _ p251 p252) (mobiusTreeCheck_join cg 1200001 1 40832 _ _ p254 p255))))))) (mobiusTreeCheck_join cg 1200001 7 40960 _ _ (mobiusTreeCheck_join cg 1200001 6 40960 _ _ (mobiusTreeCheck_join cg 1200001 5 40960 _ _ (mobiusTreeCheck_join cg 1200001 4 40960 _ _ (mobiusTreeCheck_join cg 1200001 3 40960 _ _ (mobiusTreeCheck_join cg 1200001 2 40960 _ _ (mobiusTreeCheck_join cg 1200001 1 40960 _ _ p263 p264) (mobiusTreeCheck_join cg 1200001 1 41088 _ _ p266 p267)) (mobiusTreeCheck_join cg 1200001 2 41216 _ _ (mobiusTreeCheck_join cg 1200001 1 41216 _ _ p270 p271) (mobiusTreeCheck_join cg 1200001 1 41344 _ _ p273 p274))) (mobiusTreeCheck_join cg 1200001 3 41472 _ _ (mobiusTreeCheck_join cg 1200001 2 41472 _ _ (mobiusTreeCheck_join cg 1200001 1 41472 _ _ p278 p279) (mobiusTreeCheck_join cg 1200001 1 41600 _ _ p281 p282)) (mobiusTreeCheck_join cg 1200001 2 41728 _ _ (mobiusTreeCheck_join cg 1200001 1 41728 _ _ p285 p286) (mobiusTreeCheck_join cg 1200001 1 41856 _ _ p288 p289)))) (mobiusTreeCheck_join cg 1200001 4 41984 _ _ (mobiusTreeCheck_join cg 1200001 3 41984 _ _ (mobiusTreeCheck_join cg 1200001 2 41984 _ _ (mobiusTreeCheck_join cg 1200001 1 41984 _ _ p294 p295) (mobiusTreeCheck_join cg 1200001 1 42112 _ _ p297 p298)) (mobiusTreeCheck_join cg 1200001 2 42240 _ _ (mobiusTreeCheck_join cg 1200001 1 42240 _ _ p301 p302) (mobiusTreeCheck_join cg 1200001 1 42368 _ _ p304 p305))) (mobiusTreeCheck_join cg 1200001 3 42496 _ _ (mobiusTreeCheck_join cg 1200001 2 42496 _ _ (mobiusTreeCheck_join cg 1200001 1 42496 _ _ p309 p310) (mobiusTreeCheck_join cg 1200001 1 42624 _ _ p312 p313)) (mobiusTreeCheck_join cg 1200001 2 42752 _ _ (mobiusTreeCheck_join cg 1200001 1 42752 _ _ p316 p317) (mobiusTreeCheck_join cg 1200001 1 42880 _ _ p319 p320))))) (mobiusTreeCheck_join cg 1200001 5 43008 _ _ (mobiusTreeCheck_join cg 1200001 4 43008 _ _ (mobiusTreeCheck_join cg 1200001 3 43008 _ _ (mobiusTreeCheck_join cg 1200001 2 43008 _ _ (mobiusTreeCheck_join cg 1200001 1 43008 _ _ p326 p327) (mobiusTreeCheck_join cg 1200001 1 43136 _ _ p329 p330)) (mobiusTreeCheck_join cg 1200001 2 43264 _ _ (mobiusTreeCheck_join cg 1200001 1 43264 _ _ p333 p334) (mobiusTreeCheck_join cg 1200001 1 43392 _ _ p336 p337))) (mobiusTreeCheck_join cg 1200001 3 43520 _ _ (mobiusTreeCheck_join cg 1200001 2 43520 _ _ (mobiusTreeCheck_join cg 1200001 1 43520 _ _ p341 p342) (mobiusTreeCheck_join cg 1200001 1 43648 _ _ p344 p345)) (mobiusTreeCheck_join cg 1200001 2 43776 _ _ (mobiusTreeCheck_join cg 1200001 1 43776 _ _ p348 p349) (mobiusTreeCheck_join cg 1200001 1 43904 _ _ p351 p352)))) (mobiusTreeCheck_join cg 1200001 4 44032 _ _ (mobiusTreeCheck_join cg 1200001 3 44032 _ _ (mobiusTreeCheck_join cg 1200001 2 44032 _ _ (mobiusTreeCheck_join cg 1200001 1 44032 _ _ p357 p358) (mobiusTreeCheck_join cg 1200001 1 44160 _ _ p360 p361)) (mobiusTreeCheck_join cg 1200001 2 44288 _ _ (mobiusTreeCheck_join cg 1200001 1 44288 _ _ p364 p365) (mobiusTreeCheck_join cg 1200001 1 44416 _ _ p367 p368))) (mobiusTreeCheck_join cg 1200001 3 44544 _ _ (mobiusTreeCheck_join cg 1200001 2 44544 _ _ (mobiusTreeCheck_join cg 1200001 1 44544 _ _ p372 p373) (mobiusTreeCheck_join cg 1200001 1 44672 _ _ p375 p376)) (mobiusTreeCheck_join cg 1200001 2 44800 _ _ (mobiusTreeCheck_join cg 1200001 1 44800 _ _ p379 p380) (mobiusTreeCheck_join cg 1200001 1 44928 _ _ p382 p383)))))) (mobiusTreeCheck_join cg 1200001 6 45056 _ _ (mobiusTreeCheck_join cg 1200001 5 45056 _ _ (mobiusTreeCheck_join cg 1200001 4 45056 _ _ (mobiusTreeCheck_join cg 1200001 3 45056 _ _ (mobiusTreeCheck_join cg 1200001 2 45056 _ _ (mobiusTreeCheck_join cg 1200001 1 45056 _ _ p390 p391) (mobiusTreeCheck_join cg 1200001 1 45184 _ _ p393 p394)) (mobiusTreeCheck_join cg 1200001 2 45312 _ _ (mobiusTreeCheck_join cg 1200001 1 45312 _ _ p397 p398) (mobiusTreeCheck_join cg 1200001 1 45440 _ _ p400 p401))) (mobiusTreeCheck_join cg 1200001 3 45568 _ _ (mobiusTreeCheck_join cg 1200001 2 45568 _ _ (mobiusTreeCheck_join cg 1200001 1 45568 _ _ p405 p406) (mobiusTreeCheck_join cg 1200001 1 45696 _ _ p408 p409)) (mobiusTreeCheck_join cg 1200001 2 45824 _ _ (mobiusTreeCheck_join cg 1200001 1 45824 _ _ p412 p413) (mobiusTreeCheck_join cg 1200001 1 45952 _ _ p415 p416)))) (mobiusTreeCheck_join cg 1200001 4 46080 _ _ (mobiusTreeCheck_join cg 1200001 3 46080 _ _ (mobiusTreeCheck_join cg 1200001 2 46080 _ _ (mobiusTreeCheck_join cg 1200001 1 46080 _ _ p421 p422) (mobiusTreeCheck_join cg 1200001 1 46208 _ _ p424 p425)) (mobiusTreeCheck_join cg 1200001 2 46336 _ _ (mobiusTreeCheck_join cg 1200001 1 46336 _ _ p428 p429) (mobiusTreeCheck_join cg 1200001 1 46464 _ _ p431 p432))) (mobiusTreeCheck_join cg 1200001 3 46592 _ _ (mobiusTreeCheck_join cg 1200001 2 46592 _ _ (mobiusTreeCheck_join cg 1200001 1 46592 _ _ p436 p437) (mobiusTreeCheck_join cg 1200001 1 46720 _ _ p439 p440)) (mobiusTreeCheck_join cg 1200001 2 46848 _ _ (mobiusTreeCheck_join cg 1200001 1 46848 _ _ p443 p444) (mobiusTreeCheck_join cg 1200001 1 46976 _ _ p446 p447))))) (mobiusTreeCheck_join cg 1200001 5 47104 _ _ (mobiusTreeCheck_join cg 1200001 4 47104 _ _ (mobiusTreeCheck_join cg 1200001 3 47104 _ _ (mobiusTreeCheck_join cg 1200001 2 47104 _ _ (mobiusTreeCheck_join cg 1200001 1 47104 _ _ p453 p454) (mobiusTreeCheck_join cg 1200001 1 47232 _ _ p456 p457)) (mobiusTreeCheck_join cg 1200001 2 47360 _ _ (mobiusTreeCheck_join cg 1200001 1 47360 _ _ p460 p461) (mobiusTreeCheck_join cg 1200001 1 47488 _ _ p463 p464))) (mobiusTreeCheck_join cg 1200001 3 47616 _ _ (mobiusTreeCheck_join cg 1200001 2 47616 _ _ (mobiusTreeCheck_join cg 1200001 1 47616 _ _ p468 p469) (mobiusTreeCheck_join cg 1200001 1 47744 _ _ p471 p472)) (mobiusTreeCheck_join cg 1200001 2 47872 _ _ (mobiusTreeCheck_join cg 1200001 1 47872 _ _ p475 p476) (mobiusTreeCheck_join cg 1200001 1 48000 _ _ p478 p479)))) (mobiusTreeCheck_join cg 1200001 4 48128 _ _ (mobiusTreeCheck_join cg 1200001 3 48128 _ _ (mobiusTreeCheck_join cg 1200001 2 48128 _ _ (mobiusTreeCheck_join cg 1200001 1 48128 _ _ p484 p485) (mobiusTreeCheck_join cg 1200001 1 48256 _ _ p487 p488)) (mobiusTreeCheck_join cg 1200001 2 48384 _ _ (mobiusTreeCheck_join cg 1200001 1 48384 _ _ p491 p492) (mobiusTreeCheck_join cg 1200001 1 48512 _ _ p494 p495))) (mobiusTreeCheck_join cg 1200001 3 48640 _ _ (mobiusTreeCheck_join cg 1200001 2 48640 _ _ (mobiusTreeCheck_join cg 1200001 1 48640 _ _ p499 p500) (mobiusTreeCheck_join cg 1200001 1 48768 _ _ p502 p503)) (mobiusTreeCheck_join cg 1200001 2 48896 _ _ (mobiusTreeCheck_join cg 1200001 1 48896 _ _ p506 p507) (mobiusTreeCheck_join cg 1200001 1 49024 _ _ p509 p510))))))))

end Helfgott

open Helfgott
theorem solution : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 32768 (MobiusCertTree.branch mobiusTableBlock004 mobiusTableBlock005) = true := Helfgott.combined

#print axioms solution
