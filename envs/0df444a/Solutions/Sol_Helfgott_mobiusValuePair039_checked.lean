-- Prove2me | solution 1 for Helfgott.mobiusValuePair039_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:17:43.632177+00:00
-- url     : https://prove2.me/submissions/a6ec859f-ae7a-4684-9e5a-8dd72f7146de

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

private abbrev d8 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 0
private theorem p8 : mobiusTreeCheck cg 1200001 1 638976 d8 = true := by decide +kernel

private abbrev d9 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 1
private theorem p9 : mobiusTreeCheck cg 1200001 1 639040 d9 = true := by decide +kernel

private def d7 : MobiusCertTree := .branch d8 d9
private abbrev d11 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 2
private theorem p11 : mobiusTreeCheck cg 1200001 1 639104 d11 = true := by decide +kernel

private abbrev d12 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 3
private theorem p12 : mobiusTreeCheck cg 1200001 1 639168 d12 = true := by decide +kernel

private def d10 : MobiusCertTree := .branch d11 d12
private def d6 : MobiusCertTree := .branch d7 d10
private abbrev d15 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 4
private theorem p15 : mobiusTreeCheck cg 1200001 1 639232 d15 = true := by decide +kernel

private abbrev d16 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 5
private theorem p16 : mobiusTreeCheck cg 1200001 1 639296 d16 = true := by decide +kernel

private def d14 : MobiusCertTree := .branch d15 d16
private abbrev d18 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 6
private theorem p18 : mobiusTreeCheck cg 1200001 1 639360 d18 = true := by decide +kernel

private abbrev d19 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 7
private theorem p19 : mobiusTreeCheck cg 1200001 1 639424 d19 = true := by decide +kernel

private def d17 : MobiusCertTree := .branch d18 d19
private def d13 : MobiusCertTree := .branch d14 d17
private def d5 : MobiusCertTree := .branch d6 d13
private abbrev d23 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 8
private theorem p23 : mobiusTreeCheck cg 1200001 1 639488 d23 = true := by decide +kernel

private abbrev d24 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 9
private theorem p24 : mobiusTreeCheck cg 1200001 1 639552 d24 = true := by decide +kernel

private def d22 : MobiusCertTree := .branch d23 d24
private abbrev d26 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 10
private theorem p26 : mobiusTreeCheck cg 1200001 1 639616 d26 = true := by decide +kernel

private abbrev d27 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 11
private theorem p27 : mobiusTreeCheck cg 1200001 1 639680 d27 = true := by decide +kernel

private def d25 : MobiusCertTree := .branch d26 d27
private def d21 : MobiusCertTree := .branch d22 d25
private abbrev d30 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 12
private theorem p30 : mobiusTreeCheck cg 1200001 1 639744 d30 = true := by decide +kernel

private abbrev d31 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 13
private theorem p31 : mobiusTreeCheck cg 1200001 1 639808 d31 = true := by decide +kernel

private def d29 : MobiusCertTree := .branch d30 d31
private abbrev d33 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 14
private theorem p33 : mobiusTreeCheck cg 1200001 1 639872 d33 = true := by decide +kernel

private abbrev d34 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 15
private theorem p34 : mobiusTreeCheck cg 1200001 1 639936 d34 = true := by decide +kernel

private def d32 : MobiusCertTree := .branch d33 d34
private def d28 : MobiusCertTree := .branch d29 d32
private def d20 : MobiusCertTree := .branch d21 d28
private def d4 : MobiusCertTree := .branch d5 d20
private abbrev d39 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 16
private theorem p39 : mobiusTreeCheck cg 1200001 1 640000 d39 = true := by decide +kernel

private abbrev d40 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 17
private theorem p40 : mobiusTreeCheck cg 1200001 1 640064 d40 = true := by decide +kernel

private def d38 : MobiusCertTree := .branch d39 d40
private abbrev d42 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 18
private theorem p42 : mobiusTreeCheck cg 1200001 1 640128 d42 = true := by decide +kernel

private abbrev d43 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 19
private theorem p43 : mobiusTreeCheck cg 1200001 1 640192 d43 = true := by decide +kernel

private def d41 : MobiusCertTree := .branch d42 d43
private def d37 : MobiusCertTree := .branch d38 d41
private abbrev d46 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 20
private theorem p46 : mobiusTreeCheck cg 1200001 1 640256 d46 = true := by decide +kernel

private abbrev d47 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 21
private theorem p47 : mobiusTreeCheck cg 1200001 1 640320 d47 = true := by decide +kernel

private def d45 : MobiusCertTree := .branch d46 d47
private abbrev d49 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 22
private theorem p49 : mobiusTreeCheck cg 1200001 1 640384 d49 = true := by decide +kernel

private abbrev d50 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 23
private theorem p50 : mobiusTreeCheck cg 1200001 1 640448 d50 = true := by decide +kernel

private def d48 : MobiusCertTree := .branch d49 d50
private def d44 : MobiusCertTree := .branch d45 d48
private def d36 : MobiusCertTree := .branch d37 d44
private abbrev d54 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 24
private theorem p54 : mobiusTreeCheck cg 1200001 1 640512 d54 = true := by decide +kernel

private abbrev d55 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 25
private theorem p55 : mobiusTreeCheck cg 1200001 1 640576 d55 = true := by decide +kernel

private def d53 : MobiusCertTree := .branch d54 d55
private abbrev d57 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 26
private theorem p57 : mobiusTreeCheck cg 1200001 1 640640 d57 = true := by decide +kernel

private abbrev d58 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 27
private theorem p58 : mobiusTreeCheck cg 1200001 1 640704 d58 = true := by decide +kernel

private def d56 : MobiusCertTree := .branch d57 d58
private def d52 : MobiusCertTree := .branch d53 d56
private abbrev d61 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 28
private theorem p61 : mobiusTreeCheck cg 1200001 1 640768 d61 = true := by decide +kernel

private abbrev d62 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 29
private theorem p62 : mobiusTreeCheck cg 1200001 1 640832 d62 = true := by decide +kernel

private def d60 : MobiusCertTree := .branch d61 d62
private abbrev d64 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 30
private theorem p64 : mobiusTreeCheck cg 1200001 1 640896 d64 = true := by decide +kernel

private abbrev d65 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 31
private theorem p65 : mobiusTreeCheck cg 1200001 1 640960 d65 = true := by decide +kernel

private def d63 : MobiusCertTree := .branch d64 d65
private def d59 : MobiusCertTree := .branch d60 d63
private def d51 : MobiusCertTree := .branch d52 d59
private def d35 : MobiusCertTree := .branch d36 d51
private def d3 : MobiusCertTree := .branch d4 d35
private abbrev d71 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 32
private theorem p71 : mobiusTreeCheck cg 1200001 1 641024 d71 = true := by decide +kernel

private abbrev d72 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 33
private theorem p72 : mobiusTreeCheck cg 1200001 1 641088 d72 = true := by decide +kernel

private def d70 : MobiusCertTree := .branch d71 d72
private abbrev d74 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 34
private theorem p74 : mobiusTreeCheck cg 1200001 1 641152 d74 = true := by decide +kernel

private abbrev d75 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 35
private theorem p75 : mobiusTreeCheck cg 1200001 1 641216 d75 = true := by decide +kernel

private def d73 : MobiusCertTree := .branch d74 d75
private def d69 : MobiusCertTree := .branch d70 d73
private abbrev d78 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 36
private theorem p78 : mobiusTreeCheck cg 1200001 1 641280 d78 = true := by decide +kernel

private abbrev d79 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 37
private theorem p79 : mobiusTreeCheck cg 1200001 1 641344 d79 = true := by decide +kernel

private def d77 : MobiusCertTree := .branch d78 d79
private abbrev d81 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 38
private theorem p81 : mobiusTreeCheck cg 1200001 1 641408 d81 = true := by decide +kernel

private abbrev d82 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 39
private theorem p82 : mobiusTreeCheck cg 1200001 1 641472 d82 = true := by decide +kernel

private def d80 : MobiusCertTree := .branch d81 d82
private def d76 : MobiusCertTree := .branch d77 d80
private def d68 : MobiusCertTree := .branch d69 d76
private abbrev d86 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 40
private theorem p86 : mobiusTreeCheck cg 1200001 1 641536 d86 = true := by decide +kernel

private abbrev d87 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 41
private theorem p87 : mobiusTreeCheck cg 1200001 1 641600 d87 = true := by decide +kernel

private def d85 : MobiusCertTree := .branch d86 d87
private abbrev d89 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 42
private theorem p89 : mobiusTreeCheck cg 1200001 1 641664 d89 = true := by decide +kernel

private abbrev d90 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 43
private theorem p90 : mobiusTreeCheck cg 1200001 1 641728 d90 = true := by decide +kernel

private def d88 : MobiusCertTree := .branch d89 d90
private def d84 : MobiusCertTree := .branch d85 d88
private abbrev d93 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 44
private theorem p93 : mobiusTreeCheck cg 1200001 1 641792 d93 = true := by decide +kernel

private abbrev d94 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 45
private theorem p94 : mobiusTreeCheck cg 1200001 1 641856 d94 = true := by decide +kernel

private def d92 : MobiusCertTree := .branch d93 d94
private abbrev d96 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 46
private theorem p96 : mobiusTreeCheck cg 1200001 1 641920 d96 = true := by decide +kernel

private abbrev d97 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 47
private theorem p97 : mobiusTreeCheck cg 1200001 1 641984 d97 = true := by decide +kernel

private def d95 : MobiusCertTree := .branch d96 d97
private def d91 : MobiusCertTree := .branch d92 d95
private def d83 : MobiusCertTree := .branch d84 d91
private def d67 : MobiusCertTree := .branch d68 d83
private abbrev d102 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 48
private theorem p102 : mobiusTreeCheck cg 1200001 1 642048 d102 = true := by decide +kernel

private abbrev d103 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 49
private theorem p103 : mobiusTreeCheck cg 1200001 1 642112 d103 = true := by decide +kernel

private def d101 : MobiusCertTree := .branch d102 d103
private abbrev d105 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 50
private theorem p105 : mobiusTreeCheck cg 1200001 1 642176 d105 = true := by decide +kernel

private abbrev d106 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 51
private theorem p106 : mobiusTreeCheck cg 1200001 1 642240 d106 = true := by decide +kernel

private def d104 : MobiusCertTree := .branch d105 d106
private def d100 : MobiusCertTree := .branch d101 d104
private abbrev d109 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 52
private theorem p109 : mobiusTreeCheck cg 1200001 1 642304 d109 = true := by decide +kernel

private abbrev d110 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 53
private theorem p110 : mobiusTreeCheck cg 1200001 1 642368 d110 = true := by decide +kernel

private def d108 : MobiusCertTree := .branch d109 d110
private abbrev d112 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 54
private theorem p112 : mobiusTreeCheck cg 1200001 1 642432 d112 = true := by decide +kernel

private abbrev d113 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 55
private theorem p113 : mobiusTreeCheck cg 1200001 1 642496 d113 = true := by decide +kernel

private def d111 : MobiusCertTree := .branch d112 d113
private def d107 : MobiusCertTree := .branch d108 d111
private def d99 : MobiusCertTree := .branch d100 d107
private abbrev d117 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 56
private theorem p117 : mobiusTreeCheck cg 1200001 1 642560 d117 = true := by decide +kernel

private abbrev d118 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 57
private theorem p118 : mobiusTreeCheck cg 1200001 1 642624 d118 = true := by decide +kernel

private def d116 : MobiusCertTree := .branch d117 d118
private abbrev d120 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 58
private theorem p120 : mobiusTreeCheck cg 1200001 1 642688 d120 = true := by decide +kernel

private abbrev d121 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 59
private theorem p121 : mobiusTreeCheck cg 1200001 1 642752 d121 = true := by decide +kernel

private def d119 : MobiusCertTree := .branch d120 d121
private def d115 : MobiusCertTree := .branch d116 d119
private abbrev d124 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 60
private theorem p124 : mobiusTreeCheck cg 1200001 1 642816 d124 = true := by decide +kernel

private abbrev d125 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 61
private theorem p125 : mobiusTreeCheck cg 1200001 1 642880 d125 = true := by decide +kernel

private def d123 : MobiusCertTree := .branch d124 d125
private abbrev d127 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 62
private theorem p127 : mobiusTreeCheck cg 1200001 1 642944 d127 = true := by decide +kernel

private abbrev d128 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 63
private theorem p128 : mobiusTreeCheck cg 1200001 1 643008 d128 = true := by decide +kernel

private def d126 : MobiusCertTree := .branch d127 d128
private def d122 : MobiusCertTree := .branch d123 d126
private def d114 : MobiusCertTree := .branch d115 d122
private def d98 : MobiusCertTree := .branch d99 d114
private def d66 : MobiusCertTree := .branch d67 d98
private def d2 : MobiusCertTree := .branch d3 d66
private abbrev d135 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 64
private theorem p135 : mobiusTreeCheck cg 1200001 1 643072 d135 = true := by decide +kernel

private abbrev d136 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 65
private theorem p136 : mobiusTreeCheck cg 1200001 1 643136 d136 = true := by decide +kernel

private def d134 : MobiusCertTree := .branch d135 d136
private abbrev d138 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 66
private theorem p138 : mobiusTreeCheck cg 1200001 1 643200 d138 = true := by decide +kernel

private abbrev d139 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 67
private theorem p139 : mobiusTreeCheck cg 1200001 1 643264 d139 = true := by decide +kernel

private def d137 : MobiusCertTree := .branch d138 d139
private def d133 : MobiusCertTree := .branch d134 d137
private abbrev d142 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 68
private theorem p142 : mobiusTreeCheck cg 1200001 1 643328 d142 = true := by decide +kernel

private abbrev d143 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 69
private theorem p143 : mobiusTreeCheck cg 1200001 1 643392 d143 = true := by decide +kernel

private def d141 : MobiusCertTree := .branch d142 d143
private abbrev d145 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 70
private theorem p145 : mobiusTreeCheck cg 1200001 1 643456 d145 = true := by decide +kernel

private abbrev d146 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 71
private theorem p146 : mobiusTreeCheck cg 1200001 1 643520 d146 = true := by decide +kernel

private def d144 : MobiusCertTree := .branch d145 d146
private def d140 : MobiusCertTree := .branch d141 d144
private def d132 : MobiusCertTree := .branch d133 d140
private abbrev d150 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 72
private theorem p150 : mobiusTreeCheck cg 1200001 1 643584 d150 = true := by decide +kernel

private abbrev d151 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 73
private theorem p151 : mobiusTreeCheck cg 1200001 1 643648 d151 = true := by decide +kernel

private def d149 : MobiusCertTree := .branch d150 d151
private abbrev d153 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 74
private theorem p153 : mobiusTreeCheck cg 1200001 1 643712 d153 = true := by decide +kernel

private abbrev d154 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 75
private theorem p154 : mobiusTreeCheck cg 1200001 1 643776 d154 = true := by decide +kernel

private def d152 : MobiusCertTree := .branch d153 d154
private def d148 : MobiusCertTree := .branch d149 d152
private abbrev d157 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 76
private theorem p157 : mobiusTreeCheck cg 1200001 1 643840 d157 = true := by decide +kernel

private abbrev d158 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 77
private theorem p158 : mobiusTreeCheck cg 1200001 1 643904 d158 = true := by decide +kernel

private def d156 : MobiusCertTree := .branch d157 d158
private abbrev d160 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 78
private theorem p160 : mobiusTreeCheck cg 1200001 1 643968 d160 = true := by decide +kernel

private abbrev d161 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 79
private theorem p161 : mobiusTreeCheck cg 1200001 1 644032 d161 = true := by decide +kernel

private def d159 : MobiusCertTree := .branch d160 d161
private def d155 : MobiusCertTree := .branch d156 d159
private def d147 : MobiusCertTree := .branch d148 d155
private def d131 : MobiusCertTree := .branch d132 d147
private abbrev d166 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 80
private theorem p166 : mobiusTreeCheck cg 1200001 1 644096 d166 = true := by decide +kernel

private abbrev d167 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 81
private theorem p167 : mobiusTreeCheck cg 1200001 1 644160 d167 = true := by decide +kernel

private def d165 : MobiusCertTree := .branch d166 d167
private abbrev d169 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 82
private theorem p169 : mobiusTreeCheck cg 1200001 1 644224 d169 = true := by decide +kernel

private abbrev d170 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 83
private theorem p170 : mobiusTreeCheck cg 1200001 1 644288 d170 = true := by decide +kernel

private def d168 : MobiusCertTree := .branch d169 d170
private def d164 : MobiusCertTree := .branch d165 d168
private abbrev d173 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 84
private theorem p173 : mobiusTreeCheck cg 1200001 1 644352 d173 = true := by decide +kernel

private abbrev d174 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 85
private theorem p174 : mobiusTreeCheck cg 1200001 1 644416 d174 = true := by decide +kernel

private def d172 : MobiusCertTree := .branch d173 d174
private abbrev d176 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 86
private theorem p176 : mobiusTreeCheck cg 1200001 1 644480 d176 = true := by decide +kernel

private abbrev d177 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 87
private theorem p177 : mobiusTreeCheck cg 1200001 1 644544 d177 = true := by decide +kernel

private def d175 : MobiusCertTree := .branch d176 d177
private def d171 : MobiusCertTree := .branch d172 d175
private def d163 : MobiusCertTree := .branch d164 d171
private abbrev d181 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 88
private theorem p181 : mobiusTreeCheck cg 1200001 1 644608 d181 = true := by decide +kernel

private abbrev d182 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 89
private theorem p182 : mobiusTreeCheck cg 1200001 1 644672 d182 = true := by decide +kernel

private def d180 : MobiusCertTree := .branch d181 d182
private abbrev d184 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 90
private theorem p184 : mobiusTreeCheck cg 1200001 1 644736 d184 = true := by decide +kernel

private abbrev d185 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 91
private theorem p185 : mobiusTreeCheck cg 1200001 1 644800 d185 = true := by decide +kernel

private def d183 : MobiusCertTree := .branch d184 d185
private def d179 : MobiusCertTree := .branch d180 d183
private abbrev d188 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 92
private theorem p188 : mobiusTreeCheck cg 1200001 1 644864 d188 = true := by decide +kernel

private abbrev d189 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 93
private theorem p189 : mobiusTreeCheck cg 1200001 1 644928 d189 = true := by decide +kernel

private def d187 : MobiusCertTree := .branch d188 d189
private abbrev d191 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 94
private theorem p191 : mobiusTreeCheck cg 1200001 1 644992 d191 = true := by decide +kernel

private abbrev d192 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 95
private theorem p192 : mobiusTreeCheck cg 1200001 1 645056 d192 = true := by decide +kernel

private def d190 : MobiusCertTree := .branch d191 d192
private def d186 : MobiusCertTree := .branch d187 d190
private def d178 : MobiusCertTree := .branch d179 d186
private def d162 : MobiusCertTree := .branch d163 d178
private def d130 : MobiusCertTree := .branch d131 d162
private abbrev d198 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 96
private theorem p198 : mobiusTreeCheck cg 1200001 1 645120 d198 = true := by decide +kernel

private abbrev d199 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 97
private theorem p199 : mobiusTreeCheck cg 1200001 1 645184 d199 = true := by decide +kernel

private def d197 : MobiusCertTree := .branch d198 d199
private abbrev d201 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 98
private theorem p201 : mobiusTreeCheck cg 1200001 1 645248 d201 = true := by decide +kernel

private abbrev d202 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 99
private theorem p202 : mobiusTreeCheck cg 1200001 1 645312 d202 = true := by decide +kernel

private def d200 : MobiusCertTree := .branch d201 d202
private def d196 : MobiusCertTree := .branch d197 d200
private abbrev d205 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 100
private theorem p205 : mobiusTreeCheck cg 1200001 1 645376 d205 = true := by decide +kernel

private abbrev d206 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 101
private theorem p206 : mobiusTreeCheck cg 1200001 1 645440 d206 = true := by decide +kernel

private def d204 : MobiusCertTree := .branch d205 d206
private abbrev d208 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 102
private theorem p208 : mobiusTreeCheck cg 1200001 1 645504 d208 = true := by decide +kernel

private abbrev d209 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 103
private theorem p209 : mobiusTreeCheck cg 1200001 1 645568 d209 = true := by decide +kernel

private def d207 : MobiusCertTree := .branch d208 d209
private def d203 : MobiusCertTree := .branch d204 d207
private def d195 : MobiusCertTree := .branch d196 d203
private abbrev d213 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 104
private theorem p213 : mobiusTreeCheck cg 1200001 1 645632 d213 = true := by decide +kernel

private abbrev d214 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 105
private theorem p214 : mobiusTreeCheck cg 1200001 1 645696 d214 = true := by decide +kernel

private def d212 : MobiusCertTree := .branch d213 d214
private abbrev d216 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 106
private theorem p216 : mobiusTreeCheck cg 1200001 1 645760 d216 = true := by decide +kernel

private abbrev d217 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 107
private theorem p217 : mobiusTreeCheck cg 1200001 1 645824 d217 = true := by decide +kernel

private def d215 : MobiusCertTree := .branch d216 d217
private def d211 : MobiusCertTree := .branch d212 d215
private abbrev d220 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 108
private theorem p220 : mobiusTreeCheck cg 1200001 1 645888 d220 = true := by decide +kernel

private abbrev d221 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 109
private theorem p221 : mobiusTreeCheck cg 1200001 1 645952 d221 = true := by decide +kernel

private def d219 : MobiusCertTree := .branch d220 d221
private abbrev d223 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 110
private theorem p223 : mobiusTreeCheck cg 1200001 1 646016 d223 = true := by decide +kernel

private abbrev d224 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 111
private theorem p224 : mobiusTreeCheck cg 1200001 1 646080 d224 = true := by decide +kernel

private def d222 : MobiusCertTree := .branch d223 d224
private def d218 : MobiusCertTree := .branch d219 d222
private def d210 : MobiusCertTree := .branch d211 d218
private def d194 : MobiusCertTree := .branch d195 d210
private abbrev d229 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 112
private theorem p229 : mobiusTreeCheck cg 1200001 1 646144 d229 = true := by decide +kernel

private abbrev d230 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 113
private theorem p230 : mobiusTreeCheck cg 1200001 1 646208 d230 = true := by decide +kernel

private def d228 : MobiusCertTree := .branch d229 d230
private abbrev d232 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 114
private theorem p232 : mobiusTreeCheck cg 1200001 1 646272 d232 = true := by decide +kernel

private abbrev d233 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 115
private theorem p233 : mobiusTreeCheck cg 1200001 1 646336 d233 = true := by decide +kernel

private def d231 : MobiusCertTree := .branch d232 d233
private def d227 : MobiusCertTree := .branch d228 d231
private abbrev d236 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 116
private theorem p236 : mobiusTreeCheck cg 1200001 1 646400 d236 = true := by decide +kernel

private abbrev d237 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 117
private theorem p237 : mobiusTreeCheck cg 1200001 1 646464 d237 = true := by decide +kernel

private def d235 : MobiusCertTree := .branch d236 d237
private abbrev d239 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 118
private theorem p239 : mobiusTreeCheck cg 1200001 1 646528 d239 = true := by decide +kernel

private abbrev d240 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 119
private theorem p240 : mobiusTreeCheck cg 1200001 1 646592 d240 = true := by decide +kernel

private def d238 : MobiusCertTree := .branch d239 d240
private def d234 : MobiusCertTree := .branch d235 d238
private def d226 : MobiusCertTree := .branch d227 d234
private abbrev d244 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 120
private theorem p244 : mobiusTreeCheck cg 1200001 1 646656 d244 = true := by decide +kernel

private abbrev d245 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 121
private theorem p245 : mobiusTreeCheck cg 1200001 1 646720 d245 = true := by decide +kernel

private def d243 : MobiusCertTree := .branch d244 d245
private abbrev d247 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 122
private theorem p247 : mobiusTreeCheck cg 1200001 1 646784 d247 = true := by decide +kernel

private abbrev d248 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 123
private theorem p248 : mobiusTreeCheck cg 1200001 1 646848 d248 = true := by decide +kernel

private def d246 : MobiusCertTree := .branch d247 d248
private def d242 : MobiusCertTree := .branch d243 d246
private abbrev d251 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 124
private theorem p251 : mobiusTreeCheck cg 1200001 1 646912 d251 = true := by decide +kernel

private abbrev d252 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 125
private theorem p252 : mobiusTreeCheck cg 1200001 1 646976 d252 = true := by decide +kernel

private def d250 : MobiusCertTree := .branch d251 d252
private abbrev d254 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 126
private theorem p254 : mobiusTreeCheck cg 1200001 1 647040 d254 = true := by decide +kernel

private abbrev d255 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock078 127
private theorem p255 : mobiusTreeCheck cg 1200001 1 647104 d255 = true := by decide +kernel

private def d253 : MobiusCertTree := .branch d254 d255
private def d249 : MobiusCertTree := .branch d250 d253
private def d241 : MobiusCertTree := .branch d242 d249
private def d225 : MobiusCertTree := .branch d226 d241
private def d193 : MobiusCertTree := .branch d194 d225
private def d129 : MobiusCertTree := .branch d130 d193
private def d1 : MobiusCertTree := .branch d2 d129
private abbrev d263 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 0
private theorem p263 : mobiusTreeCheck cg 1200001 1 647168 d263 = true := by decide +kernel

private abbrev d264 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 1
private theorem p264 : mobiusTreeCheck cg 1200001 1 647232 d264 = true := by decide +kernel

private def d262 : MobiusCertTree := .branch d263 d264
private abbrev d266 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 2
private theorem p266 : mobiusTreeCheck cg 1200001 1 647296 d266 = true := by decide +kernel

private abbrev d267 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 3
private theorem p267 : mobiusTreeCheck cg 1200001 1 647360 d267 = true := by decide +kernel

private def d265 : MobiusCertTree := .branch d266 d267
private def d261 : MobiusCertTree := .branch d262 d265
private abbrev d270 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 4
private theorem p270 : mobiusTreeCheck cg 1200001 1 647424 d270 = true := by decide +kernel

private abbrev d271 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 5
private theorem p271 : mobiusTreeCheck cg 1200001 1 647488 d271 = true := by decide +kernel

private def d269 : MobiusCertTree := .branch d270 d271
private abbrev d273 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 6
private theorem p273 : mobiusTreeCheck cg 1200001 1 647552 d273 = true := by decide +kernel

private abbrev d274 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 7
private theorem p274 : mobiusTreeCheck cg 1200001 1 647616 d274 = true := by decide +kernel

private def d272 : MobiusCertTree := .branch d273 d274
private def d268 : MobiusCertTree := .branch d269 d272
private def d260 : MobiusCertTree := .branch d261 d268
private abbrev d278 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 8
private theorem p278 : mobiusTreeCheck cg 1200001 1 647680 d278 = true := by decide +kernel

private abbrev d279 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 9
private theorem p279 : mobiusTreeCheck cg 1200001 1 647744 d279 = true := by decide +kernel

private def d277 : MobiusCertTree := .branch d278 d279
private abbrev d281 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 10
private theorem p281 : mobiusTreeCheck cg 1200001 1 647808 d281 = true := by decide +kernel

private abbrev d282 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 11
private theorem p282 : mobiusTreeCheck cg 1200001 1 647872 d282 = true := by decide +kernel

private def d280 : MobiusCertTree := .branch d281 d282
private def d276 : MobiusCertTree := .branch d277 d280
private abbrev d285 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 12
private theorem p285 : mobiusTreeCheck cg 1200001 1 647936 d285 = true := by decide +kernel

private abbrev d286 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 13
private theorem p286 : mobiusTreeCheck cg 1200001 1 648000 d286 = true := by decide +kernel

private def d284 : MobiusCertTree := .branch d285 d286
private abbrev d288 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 14
private theorem p288 : mobiusTreeCheck cg 1200001 1 648064 d288 = true := by decide +kernel

private abbrev d289 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 15
private theorem p289 : mobiusTreeCheck cg 1200001 1 648128 d289 = true := by decide +kernel

private def d287 : MobiusCertTree := .branch d288 d289
private def d283 : MobiusCertTree := .branch d284 d287
private def d275 : MobiusCertTree := .branch d276 d283
private def d259 : MobiusCertTree := .branch d260 d275
private abbrev d294 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 16
private theorem p294 : mobiusTreeCheck cg 1200001 1 648192 d294 = true := by decide +kernel

private abbrev d295 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 17
private theorem p295 : mobiusTreeCheck cg 1200001 1 648256 d295 = true := by decide +kernel

private def d293 : MobiusCertTree := .branch d294 d295
private abbrev d297 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 18
private theorem p297 : mobiusTreeCheck cg 1200001 1 648320 d297 = true := by decide +kernel

private abbrev d298 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 19
private theorem p298 : mobiusTreeCheck cg 1200001 1 648384 d298 = true := by decide +kernel

private def d296 : MobiusCertTree := .branch d297 d298
private def d292 : MobiusCertTree := .branch d293 d296
private abbrev d301 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 20
private theorem p301 : mobiusTreeCheck cg 1200001 1 648448 d301 = true := by decide +kernel

private abbrev d302 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 21
private theorem p302 : mobiusTreeCheck cg 1200001 1 648512 d302 = true := by decide +kernel

private def d300 : MobiusCertTree := .branch d301 d302
private abbrev d304 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 22
private theorem p304 : mobiusTreeCheck cg 1200001 1 648576 d304 = true := by decide +kernel

private abbrev d305 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 23
private theorem p305 : mobiusTreeCheck cg 1200001 1 648640 d305 = true := by decide +kernel

private def d303 : MobiusCertTree := .branch d304 d305
private def d299 : MobiusCertTree := .branch d300 d303
private def d291 : MobiusCertTree := .branch d292 d299
private abbrev d309 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 24
private theorem p309 : mobiusTreeCheck cg 1200001 1 648704 d309 = true := by decide +kernel

private abbrev d310 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 25
private theorem p310 : mobiusTreeCheck cg 1200001 1 648768 d310 = true := by decide +kernel

private def d308 : MobiusCertTree := .branch d309 d310
private abbrev d312 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 26
private theorem p312 : mobiusTreeCheck cg 1200001 1 648832 d312 = true := by decide +kernel

private abbrev d313 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 27
private theorem p313 : mobiusTreeCheck cg 1200001 1 648896 d313 = true := by decide +kernel

private def d311 : MobiusCertTree := .branch d312 d313
private def d307 : MobiusCertTree := .branch d308 d311
private abbrev d316 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 28
private theorem p316 : mobiusTreeCheck cg 1200001 1 648960 d316 = true := by decide +kernel

private abbrev d317 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 29
private theorem p317 : mobiusTreeCheck cg 1200001 1 649024 d317 = true := by decide +kernel

private def d315 : MobiusCertTree := .branch d316 d317
private abbrev d319 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 30
private theorem p319 : mobiusTreeCheck cg 1200001 1 649088 d319 = true := by decide +kernel

private abbrev d320 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 31
private theorem p320 : mobiusTreeCheck cg 1200001 1 649152 d320 = true := by decide +kernel

private def d318 : MobiusCertTree := .branch d319 d320
private def d314 : MobiusCertTree := .branch d315 d318
private def d306 : MobiusCertTree := .branch d307 d314
private def d290 : MobiusCertTree := .branch d291 d306
private def d258 : MobiusCertTree := .branch d259 d290
private abbrev d326 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 32
private theorem p326 : mobiusTreeCheck cg 1200001 1 649216 d326 = true := by decide +kernel

private abbrev d327 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 33
private theorem p327 : mobiusTreeCheck cg 1200001 1 649280 d327 = true := by decide +kernel

private def d325 : MobiusCertTree := .branch d326 d327
private abbrev d329 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 34
private theorem p329 : mobiusTreeCheck cg 1200001 1 649344 d329 = true := by decide +kernel

private abbrev d330 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 35
private theorem p330 : mobiusTreeCheck cg 1200001 1 649408 d330 = true := by decide +kernel

private def d328 : MobiusCertTree := .branch d329 d330
private def d324 : MobiusCertTree := .branch d325 d328
private abbrev d333 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 36
private theorem p333 : mobiusTreeCheck cg 1200001 1 649472 d333 = true := by decide +kernel

private abbrev d334 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 37
private theorem p334 : mobiusTreeCheck cg 1200001 1 649536 d334 = true := by decide +kernel

private def d332 : MobiusCertTree := .branch d333 d334
private abbrev d336 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 38
private theorem p336 : mobiusTreeCheck cg 1200001 1 649600 d336 = true := by decide +kernel

private abbrev d337 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 39
private theorem p337 : mobiusTreeCheck cg 1200001 1 649664 d337 = true := by decide +kernel

private def d335 : MobiusCertTree := .branch d336 d337
private def d331 : MobiusCertTree := .branch d332 d335
private def d323 : MobiusCertTree := .branch d324 d331
private abbrev d341 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 40
private theorem p341 : mobiusTreeCheck cg 1200001 1 649728 d341 = true := by decide +kernel

private abbrev d342 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 41
private theorem p342 : mobiusTreeCheck cg 1200001 1 649792 d342 = true := by decide +kernel

private def d340 : MobiusCertTree := .branch d341 d342
private abbrev d344 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 42
private theorem p344 : mobiusTreeCheck cg 1200001 1 649856 d344 = true := by decide +kernel

private abbrev d345 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 43
private theorem p345 : mobiusTreeCheck cg 1200001 1 649920 d345 = true := by decide +kernel

private def d343 : MobiusCertTree := .branch d344 d345
private def d339 : MobiusCertTree := .branch d340 d343
private abbrev d348 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 44
private theorem p348 : mobiusTreeCheck cg 1200001 1 649984 d348 = true := by decide +kernel

private abbrev d349 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 45
private theorem p349 : mobiusTreeCheck cg 1200001 1 650048 d349 = true := by decide +kernel

private def d347 : MobiusCertTree := .branch d348 d349
private abbrev d351 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 46
private theorem p351 : mobiusTreeCheck cg 1200001 1 650112 d351 = true := by decide +kernel

private abbrev d352 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 47
private theorem p352 : mobiusTreeCheck cg 1200001 1 650176 d352 = true := by decide +kernel

private def d350 : MobiusCertTree := .branch d351 d352
private def d346 : MobiusCertTree := .branch d347 d350
private def d338 : MobiusCertTree := .branch d339 d346
private def d322 : MobiusCertTree := .branch d323 d338
private abbrev d357 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 48
private theorem p357 : mobiusTreeCheck cg 1200001 1 650240 d357 = true := by decide +kernel

private abbrev d358 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 49
private theorem p358 : mobiusTreeCheck cg 1200001 1 650304 d358 = true := by decide +kernel

private def d356 : MobiusCertTree := .branch d357 d358
private abbrev d360 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 50
private theorem p360 : mobiusTreeCheck cg 1200001 1 650368 d360 = true := by decide +kernel

private abbrev d361 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 51
private theorem p361 : mobiusTreeCheck cg 1200001 1 650432 d361 = true := by decide +kernel

private def d359 : MobiusCertTree := .branch d360 d361
private def d355 : MobiusCertTree := .branch d356 d359
private abbrev d364 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 52
private theorem p364 : mobiusTreeCheck cg 1200001 1 650496 d364 = true := by decide +kernel

private abbrev d365 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 53
private theorem p365 : mobiusTreeCheck cg 1200001 1 650560 d365 = true := by decide +kernel

private def d363 : MobiusCertTree := .branch d364 d365
private abbrev d367 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 54
private theorem p367 : mobiusTreeCheck cg 1200001 1 650624 d367 = true := by decide +kernel

private abbrev d368 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 55
private theorem p368 : mobiusTreeCheck cg 1200001 1 650688 d368 = true := by decide +kernel

private def d366 : MobiusCertTree := .branch d367 d368
private def d362 : MobiusCertTree := .branch d363 d366
private def d354 : MobiusCertTree := .branch d355 d362
private abbrev d372 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 56
private theorem p372 : mobiusTreeCheck cg 1200001 1 650752 d372 = true := by decide +kernel

private abbrev d373 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 57
private theorem p373 : mobiusTreeCheck cg 1200001 1 650816 d373 = true := by decide +kernel

private def d371 : MobiusCertTree := .branch d372 d373
private abbrev d375 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 58
private theorem p375 : mobiusTreeCheck cg 1200001 1 650880 d375 = true := by decide +kernel

private abbrev d376 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 59
private theorem p376 : mobiusTreeCheck cg 1200001 1 650944 d376 = true := by decide +kernel

private def d374 : MobiusCertTree := .branch d375 d376
private def d370 : MobiusCertTree := .branch d371 d374
private abbrev d379 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 60
private theorem p379 : mobiusTreeCheck cg 1200001 1 651008 d379 = true := by decide +kernel

private abbrev d380 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 61
private theorem p380 : mobiusTreeCheck cg 1200001 1 651072 d380 = true := by decide +kernel

private def d378 : MobiusCertTree := .branch d379 d380
private abbrev d382 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 62
private theorem p382 : mobiusTreeCheck cg 1200001 1 651136 d382 = true := by decide +kernel

private abbrev d383 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 63
private theorem p383 : mobiusTreeCheck cg 1200001 1 651200 d383 = true := by decide +kernel

private def d381 : MobiusCertTree := .branch d382 d383
private def d377 : MobiusCertTree := .branch d378 d381
private def d369 : MobiusCertTree := .branch d370 d377
private def d353 : MobiusCertTree := .branch d354 d369
private def d321 : MobiusCertTree := .branch d322 d353
private def d257 : MobiusCertTree := .branch d258 d321
private abbrev d390 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 64
private theorem p390 : mobiusTreeCheck cg 1200001 1 651264 d390 = true := by decide +kernel

private abbrev d391 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 65
private theorem p391 : mobiusTreeCheck cg 1200001 1 651328 d391 = true := by decide +kernel

private def d389 : MobiusCertTree := .branch d390 d391
private abbrev d393 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 66
private theorem p393 : mobiusTreeCheck cg 1200001 1 651392 d393 = true := by decide +kernel

private abbrev d394 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 67
private theorem p394 : mobiusTreeCheck cg 1200001 1 651456 d394 = true := by decide +kernel

private def d392 : MobiusCertTree := .branch d393 d394
private def d388 : MobiusCertTree := .branch d389 d392
private abbrev d397 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 68
private theorem p397 : mobiusTreeCheck cg 1200001 1 651520 d397 = true := by decide +kernel

private abbrev d398 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 69
private theorem p398 : mobiusTreeCheck cg 1200001 1 651584 d398 = true := by decide +kernel

private def d396 : MobiusCertTree := .branch d397 d398
private abbrev d400 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 70
private theorem p400 : mobiusTreeCheck cg 1200001 1 651648 d400 = true := by decide +kernel

private abbrev d401 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 71
private theorem p401 : mobiusTreeCheck cg 1200001 1 651712 d401 = true := by decide +kernel

private def d399 : MobiusCertTree := .branch d400 d401
private def d395 : MobiusCertTree := .branch d396 d399
private def d387 : MobiusCertTree := .branch d388 d395
private abbrev d405 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 72
private theorem p405 : mobiusTreeCheck cg 1200001 1 651776 d405 = true := by decide +kernel

private abbrev d406 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 73
private theorem p406 : mobiusTreeCheck cg 1200001 1 651840 d406 = true := by decide +kernel

private def d404 : MobiusCertTree := .branch d405 d406
private abbrev d408 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 74
private theorem p408 : mobiusTreeCheck cg 1200001 1 651904 d408 = true := by decide +kernel

private abbrev d409 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 75
private theorem p409 : mobiusTreeCheck cg 1200001 1 651968 d409 = true := by decide +kernel

private def d407 : MobiusCertTree := .branch d408 d409
private def d403 : MobiusCertTree := .branch d404 d407
private abbrev d412 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 76
private theorem p412 : mobiusTreeCheck cg 1200001 1 652032 d412 = true := by decide +kernel

private abbrev d413 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 77
private theorem p413 : mobiusTreeCheck cg 1200001 1 652096 d413 = true := by decide +kernel

private def d411 : MobiusCertTree := .branch d412 d413
private abbrev d415 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 78
private theorem p415 : mobiusTreeCheck cg 1200001 1 652160 d415 = true := by decide +kernel

private abbrev d416 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 79
private theorem p416 : mobiusTreeCheck cg 1200001 1 652224 d416 = true := by decide +kernel

private def d414 : MobiusCertTree := .branch d415 d416
private def d410 : MobiusCertTree := .branch d411 d414
private def d402 : MobiusCertTree := .branch d403 d410
private def d386 : MobiusCertTree := .branch d387 d402
private abbrev d421 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 80
private theorem p421 : mobiusTreeCheck cg 1200001 1 652288 d421 = true := by decide +kernel

private abbrev d422 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 81
private theorem p422 : mobiusTreeCheck cg 1200001 1 652352 d422 = true := by decide +kernel

private def d420 : MobiusCertTree := .branch d421 d422
private abbrev d424 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 82
private theorem p424 : mobiusTreeCheck cg 1200001 1 652416 d424 = true := by decide +kernel

private abbrev d425 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 83
private theorem p425 : mobiusTreeCheck cg 1200001 1 652480 d425 = true := by decide +kernel

private def d423 : MobiusCertTree := .branch d424 d425
private def d419 : MobiusCertTree := .branch d420 d423
private abbrev d428 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 84
private theorem p428 : mobiusTreeCheck cg 1200001 1 652544 d428 = true := by decide +kernel

private abbrev d429 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 85
private theorem p429 : mobiusTreeCheck cg 1200001 1 652608 d429 = true := by decide +kernel

private def d427 : MobiusCertTree := .branch d428 d429
private abbrev d431 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 86
private theorem p431 : mobiusTreeCheck cg 1200001 1 652672 d431 = true := by decide +kernel

private abbrev d432 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 87
private theorem p432 : mobiusTreeCheck cg 1200001 1 652736 d432 = true := by decide +kernel

private def d430 : MobiusCertTree := .branch d431 d432
private def d426 : MobiusCertTree := .branch d427 d430
private def d418 : MobiusCertTree := .branch d419 d426
private abbrev d436 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 88
private theorem p436 : mobiusTreeCheck cg 1200001 1 652800 d436 = true := by decide +kernel

private abbrev d437 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 89
private theorem p437 : mobiusTreeCheck cg 1200001 1 652864 d437 = true := by decide +kernel

private def d435 : MobiusCertTree := .branch d436 d437
private abbrev d439 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 90
private theorem p439 : mobiusTreeCheck cg 1200001 1 652928 d439 = true := by decide +kernel

private abbrev d440 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 91
private theorem p440 : mobiusTreeCheck cg 1200001 1 652992 d440 = true := by decide +kernel

private def d438 : MobiusCertTree := .branch d439 d440
private def d434 : MobiusCertTree := .branch d435 d438
private abbrev d443 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 92
private theorem p443 : mobiusTreeCheck cg 1200001 1 653056 d443 = true := by decide +kernel

private abbrev d444 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 93
private theorem p444 : mobiusTreeCheck cg 1200001 1 653120 d444 = true := by decide +kernel

private def d442 : MobiusCertTree := .branch d443 d444
private abbrev d446 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 94
private theorem p446 : mobiusTreeCheck cg 1200001 1 653184 d446 = true := by decide +kernel

private abbrev d447 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 95
private theorem p447 : mobiusTreeCheck cg 1200001 1 653248 d447 = true := by decide +kernel

private def d445 : MobiusCertTree := .branch d446 d447
private def d441 : MobiusCertTree := .branch d442 d445
private def d433 : MobiusCertTree := .branch d434 d441
private def d417 : MobiusCertTree := .branch d418 d433
private def d385 : MobiusCertTree := .branch d386 d417
private abbrev d453 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 96
private theorem p453 : mobiusTreeCheck cg 1200001 1 653312 d453 = true := by decide +kernel

private abbrev d454 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 97
private theorem p454 : mobiusTreeCheck cg 1200001 1 653376 d454 = true := by decide +kernel

private def d452 : MobiusCertTree := .branch d453 d454
private abbrev d456 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 98
private theorem p456 : mobiusTreeCheck cg 1200001 1 653440 d456 = true := by decide +kernel

private abbrev d457 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 99
private theorem p457 : mobiusTreeCheck cg 1200001 1 653504 d457 = true := by decide +kernel

private def d455 : MobiusCertTree := .branch d456 d457
private def d451 : MobiusCertTree := .branch d452 d455
private abbrev d460 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 100
private theorem p460 : mobiusTreeCheck cg 1200001 1 653568 d460 = true := by decide +kernel

private abbrev d461 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 101
private theorem p461 : mobiusTreeCheck cg 1200001 1 653632 d461 = true := by decide +kernel

private def d459 : MobiusCertTree := .branch d460 d461
private abbrev d463 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 102
private theorem p463 : mobiusTreeCheck cg 1200001 1 653696 d463 = true := by decide +kernel

private abbrev d464 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 103
private theorem p464 : mobiusTreeCheck cg 1200001 1 653760 d464 = true := by decide +kernel

private def d462 : MobiusCertTree := .branch d463 d464
private def d458 : MobiusCertTree := .branch d459 d462
private def d450 : MobiusCertTree := .branch d451 d458
private abbrev d468 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 104
private theorem p468 : mobiusTreeCheck cg 1200001 1 653824 d468 = true := by decide +kernel

private abbrev d469 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 105
private theorem p469 : mobiusTreeCheck cg 1200001 1 653888 d469 = true := by decide +kernel

private def d467 : MobiusCertTree := .branch d468 d469
private abbrev d471 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 106
private theorem p471 : mobiusTreeCheck cg 1200001 1 653952 d471 = true := by decide +kernel

private abbrev d472 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 107
private theorem p472 : mobiusTreeCheck cg 1200001 1 654016 d472 = true := by decide +kernel

private def d470 : MobiusCertTree := .branch d471 d472
private def d466 : MobiusCertTree := .branch d467 d470
private abbrev d475 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 108
private theorem p475 : mobiusTreeCheck cg 1200001 1 654080 d475 = true := by decide +kernel

private abbrev d476 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 109
private theorem p476 : mobiusTreeCheck cg 1200001 1 654144 d476 = true := by decide +kernel

private def d474 : MobiusCertTree := .branch d475 d476
private abbrev d478 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 110
private theorem p478 : mobiusTreeCheck cg 1200001 1 654208 d478 = true := by decide +kernel

private abbrev d479 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 111
private theorem p479 : mobiusTreeCheck cg 1200001 1 654272 d479 = true := by decide +kernel

private def d477 : MobiusCertTree := .branch d478 d479
private def d473 : MobiusCertTree := .branch d474 d477
private def d465 : MobiusCertTree := .branch d466 d473
private def d449 : MobiusCertTree := .branch d450 d465
private abbrev d484 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 112
private theorem p484 : mobiusTreeCheck cg 1200001 1 654336 d484 = true := by decide +kernel

private abbrev d485 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 113
private theorem p485 : mobiusTreeCheck cg 1200001 1 654400 d485 = true := by decide +kernel

private def d483 : MobiusCertTree := .branch d484 d485
private abbrev d487 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 114
private theorem p487 : mobiusTreeCheck cg 1200001 1 654464 d487 = true := by decide +kernel

private abbrev d488 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 115
private theorem p488 : mobiusTreeCheck cg 1200001 1 654528 d488 = true := by decide +kernel

private def d486 : MobiusCertTree := .branch d487 d488
private def d482 : MobiusCertTree := .branch d483 d486
private abbrev d491 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 116
private theorem p491 : mobiusTreeCheck cg 1200001 1 654592 d491 = true := by decide +kernel

private abbrev d492 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 117
private theorem p492 : mobiusTreeCheck cg 1200001 1 654656 d492 = true := by decide +kernel

private def d490 : MobiusCertTree := .branch d491 d492
private abbrev d494 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 118
private theorem p494 : mobiusTreeCheck cg 1200001 1 654720 d494 = true := by decide +kernel

private abbrev d495 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 119
private theorem p495 : mobiusTreeCheck cg 1200001 1 654784 d495 = true := by decide +kernel

private def d493 : MobiusCertTree := .branch d494 d495
private def d489 : MobiusCertTree := .branch d490 d493
private def d481 : MobiusCertTree := .branch d482 d489
private abbrev d499 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 120
private theorem p499 : mobiusTreeCheck cg 1200001 1 654848 d499 = true := by decide +kernel

private abbrev d500 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 121
private theorem p500 : mobiusTreeCheck cg 1200001 1 654912 d500 = true := by decide +kernel

private def d498 : MobiusCertTree := .branch d499 d500
private abbrev d502 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 122
private theorem p502 : mobiusTreeCheck cg 1200001 1 654976 d502 = true := by decide +kernel

private abbrev d503 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 123
private theorem p503 : mobiusTreeCheck cg 1200001 1 655040 d503 = true := by decide +kernel

private def d501 : MobiusCertTree := .branch d502 d503
private def d497 : MobiusCertTree := .branch d498 d501
private abbrev d506 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 124
private theorem p506 : mobiusTreeCheck cg 1200001 1 655104 d506 = true := by decide +kernel

private abbrev d507 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 125
private theorem p507 : mobiusTreeCheck cg 1200001 1 655168 d507 = true := by decide +kernel

private def d505 : MobiusCertTree := .branch d506 d507
private abbrev d509 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 126
private theorem p509 : mobiusTreeCheck cg 1200001 1 655232 d509 = true := by decide +kernel

private abbrev d510 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock079 127
private theorem p510 : mobiusTreeCheck cg 1200001 1 655296 d510 = true := by decide +kernel

private def d508 : MobiusCertTree := .branch d509 d510
private def d504 : MobiusCertTree := .branch d505 d508
private def d496 : MobiusCertTree := .branch d497 d504
private def d480 : MobiusCertTree := .branch d481 d496
private def d448 : MobiusCertTree := .branch d449 d480
private def d384 : MobiusCertTree := .branch d385 d448
private def d256 : MobiusCertTree := .branch d257 d384
private def d0 : MobiusCertTree := .branch d1 d256

private theorem combined : mobiusTreeCheck cg 1200001 9 638976 d0 = true :=
  (mobiusTreeCheck_join cg 1200001 8 638976 _ _ (mobiusTreeCheck_join cg 1200001 7 638976 _ _ (mobiusTreeCheck_join cg 1200001 6 638976 _ _ (mobiusTreeCheck_join cg 1200001 5 638976 _ _ (mobiusTreeCheck_join cg 1200001 4 638976 _ _ (mobiusTreeCheck_join cg 1200001 3 638976 _ _ (mobiusTreeCheck_join cg 1200001 2 638976 _ _ (mobiusTreeCheck_join cg 1200001 1 638976 _ _ p8 p9) (mobiusTreeCheck_join cg 1200001 1 639104 _ _ p11 p12)) (mobiusTreeCheck_join cg 1200001 2 639232 _ _ (mobiusTreeCheck_join cg 1200001 1 639232 _ _ p15 p16) (mobiusTreeCheck_join cg 1200001 1 639360 _ _ p18 p19))) (mobiusTreeCheck_join cg 1200001 3 639488 _ _ (mobiusTreeCheck_join cg 1200001 2 639488 _ _ (mobiusTreeCheck_join cg 1200001 1 639488 _ _ p23 p24) (mobiusTreeCheck_join cg 1200001 1 639616 _ _ p26 p27)) (mobiusTreeCheck_join cg 1200001 2 639744 _ _ (mobiusTreeCheck_join cg 1200001 1 639744 _ _ p30 p31) (mobiusTreeCheck_join cg 1200001 1 639872 _ _ p33 p34)))) (mobiusTreeCheck_join cg 1200001 4 640000 _ _ (mobiusTreeCheck_join cg 1200001 3 640000 _ _ (mobiusTreeCheck_join cg 1200001 2 640000 _ _ (mobiusTreeCheck_join cg 1200001 1 640000 _ _ p39 p40) (mobiusTreeCheck_join cg 1200001 1 640128 _ _ p42 p43)) (mobiusTreeCheck_join cg 1200001 2 640256 _ _ (mobiusTreeCheck_join cg 1200001 1 640256 _ _ p46 p47) (mobiusTreeCheck_join cg 1200001 1 640384 _ _ p49 p50))) (mobiusTreeCheck_join cg 1200001 3 640512 _ _ (mobiusTreeCheck_join cg 1200001 2 640512 _ _ (mobiusTreeCheck_join cg 1200001 1 640512 _ _ p54 p55) (mobiusTreeCheck_join cg 1200001 1 640640 _ _ p57 p58)) (mobiusTreeCheck_join cg 1200001 2 640768 _ _ (mobiusTreeCheck_join cg 1200001 1 640768 _ _ p61 p62) (mobiusTreeCheck_join cg 1200001 1 640896 _ _ p64 p65))))) (mobiusTreeCheck_join cg 1200001 5 641024 _ _ (mobiusTreeCheck_join cg 1200001 4 641024 _ _ (mobiusTreeCheck_join cg 1200001 3 641024 _ _ (mobiusTreeCheck_join cg 1200001 2 641024 _ _ (mobiusTreeCheck_join cg 1200001 1 641024 _ _ p71 p72) (mobiusTreeCheck_join cg 1200001 1 641152 _ _ p74 p75)) (mobiusTreeCheck_join cg 1200001 2 641280 _ _ (mobiusTreeCheck_join cg 1200001 1 641280 _ _ p78 p79) (mobiusTreeCheck_join cg 1200001 1 641408 _ _ p81 p82))) (mobiusTreeCheck_join cg 1200001 3 641536 _ _ (mobiusTreeCheck_join cg 1200001 2 641536 _ _ (mobiusTreeCheck_join cg 1200001 1 641536 _ _ p86 p87) (mobiusTreeCheck_join cg 1200001 1 641664 _ _ p89 p90)) (mobiusTreeCheck_join cg 1200001 2 641792 _ _ (mobiusTreeCheck_join cg 1200001 1 641792 _ _ p93 p94) (mobiusTreeCheck_join cg 1200001 1 641920 _ _ p96 p97)))) (mobiusTreeCheck_join cg 1200001 4 642048 _ _ (mobiusTreeCheck_join cg 1200001 3 642048 _ _ (mobiusTreeCheck_join cg 1200001 2 642048 _ _ (mobiusTreeCheck_join cg 1200001 1 642048 _ _ p102 p103) (mobiusTreeCheck_join cg 1200001 1 642176 _ _ p105 p106)) (mobiusTreeCheck_join cg 1200001 2 642304 _ _ (mobiusTreeCheck_join cg 1200001 1 642304 _ _ p109 p110) (mobiusTreeCheck_join cg 1200001 1 642432 _ _ p112 p113))) (mobiusTreeCheck_join cg 1200001 3 642560 _ _ (mobiusTreeCheck_join cg 1200001 2 642560 _ _ (mobiusTreeCheck_join cg 1200001 1 642560 _ _ p117 p118) (mobiusTreeCheck_join cg 1200001 1 642688 _ _ p120 p121)) (mobiusTreeCheck_join cg 1200001 2 642816 _ _ (mobiusTreeCheck_join cg 1200001 1 642816 _ _ p124 p125) (mobiusTreeCheck_join cg 1200001 1 642944 _ _ p127 p128)))))) (mobiusTreeCheck_join cg 1200001 6 643072 _ _ (mobiusTreeCheck_join cg 1200001 5 643072 _ _ (mobiusTreeCheck_join cg 1200001 4 643072 _ _ (mobiusTreeCheck_join cg 1200001 3 643072 _ _ (mobiusTreeCheck_join cg 1200001 2 643072 _ _ (mobiusTreeCheck_join cg 1200001 1 643072 _ _ p135 p136) (mobiusTreeCheck_join cg 1200001 1 643200 _ _ p138 p139)) (mobiusTreeCheck_join cg 1200001 2 643328 _ _ (mobiusTreeCheck_join cg 1200001 1 643328 _ _ p142 p143) (mobiusTreeCheck_join cg 1200001 1 643456 _ _ p145 p146))) (mobiusTreeCheck_join cg 1200001 3 643584 _ _ (mobiusTreeCheck_join cg 1200001 2 643584 _ _ (mobiusTreeCheck_join cg 1200001 1 643584 _ _ p150 p151) (mobiusTreeCheck_join cg 1200001 1 643712 _ _ p153 p154)) (mobiusTreeCheck_join cg 1200001 2 643840 _ _ (mobiusTreeCheck_join cg 1200001 1 643840 _ _ p157 p158) (mobiusTreeCheck_join cg 1200001 1 643968 _ _ p160 p161)))) (mobiusTreeCheck_join cg 1200001 4 644096 _ _ (mobiusTreeCheck_join cg 1200001 3 644096 _ _ (mobiusTreeCheck_join cg 1200001 2 644096 _ _ (mobiusTreeCheck_join cg 1200001 1 644096 _ _ p166 p167) (mobiusTreeCheck_join cg 1200001 1 644224 _ _ p169 p170)) (mobiusTreeCheck_join cg 1200001 2 644352 _ _ (mobiusTreeCheck_join cg 1200001 1 644352 _ _ p173 p174) (mobiusTreeCheck_join cg 1200001 1 644480 _ _ p176 p177))) (mobiusTreeCheck_join cg 1200001 3 644608 _ _ (mobiusTreeCheck_join cg 1200001 2 644608 _ _ (mobiusTreeCheck_join cg 1200001 1 644608 _ _ p181 p182) (mobiusTreeCheck_join cg 1200001 1 644736 _ _ p184 p185)) (mobiusTreeCheck_join cg 1200001 2 644864 _ _ (mobiusTreeCheck_join cg 1200001 1 644864 _ _ p188 p189) (mobiusTreeCheck_join cg 1200001 1 644992 _ _ p191 p192))))) (mobiusTreeCheck_join cg 1200001 5 645120 _ _ (mobiusTreeCheck_join cg 1200001 4 645120 _ _ (mobiusTreeCheck_join cg 1200001 3 645120 _ _ (mobiusTreeCheck_join cg 1200001 2 645120 _ _ (mobiusTreeCheck_join cg 1200001 1 645120 _ _ p198 p199) (mobiusTreeCheck_join cg 1200001 1 645248 _ _ p201 p202)) (mobiusTreeCheck_join cg 1200001 2 645376 _ _ (mobiusTreeCheck_join cg 1200001 1 645376 _ _ p205 p206) (mobiusTreeCheck_join cg 1200001 1 645504 _ _ p208 p209))) (mobiusTreeCheck_join cg 1200001 3 645632 _ _ (mobiusTreeCheck_join cg 1200001 2 645632 _ _ (mobiusTreeCheck_join cg 1200001 1 645632 _ _ p213 p214) (mobiusTreeCheck_join cg 1200001 1 645760 _ _ p216 p217)) (mobiusTreeCheck_join cg 1200001 2 645888 _ _ (mobiusTreeCheck_join cg 1200001 1 645888 _ _ p220 p221) (mobiusTreeCheck_join cg 1200001 1 646016 _ _ p223 p224)))) (mobiusTreeCheck_join cg 1200001 4 646144 _ _ (mobiusTreeCheck_join cg 1200001 3 646144 _ _ (mobiusTreeCheck_join cg 1200001 2 646144 _ _ (mobiusTreeCheck_join cg 1200001 1 646144 _ _ p229 p230) (mobiusTreeCheck_join cg 1200001 1 646272 _ _ p232 p233)) (mobiusTreeCheck_join cg 1200001 2 646400 _ _ (mobiusTreeCheck_join cg 1200001 1 646400 _ _ p236 p237) (mobiusTreeCheck_join cg 1200001 1 646528 _ _ p239 p240))) (mobiusTreeCheck_join cg 1200001 3 646656 _ _ (mobiusTreeCheck_join cg 1200001 2 646656 _ _ (mobiusTreeCheck_join cg 1200001 1 646656 _ _ p244 p245) (mobiusTreeCheck_join cg 1200001 1 646784 _ _ p247 p248)) (mobiusTreeCheck_join cg 1200001 2 646912 _ _ (mobiusTreeCheck_join cg 1200001 1 646912 _ _ p251 p252) (mobiusTreeCheck_join cg 1200001 1 647040 _ _ p254 p255))))))) (mobiusTreeCheck_join cg 1200001 7 647168 _ _ (mobiusTreeCheck_join cg 1200001 6 647168 _ _ (mobiusTreeCheck_join cg 1200001 5 647168 _ _ (mobiusTreeCheck_join cg 1200001 4 647168 _ _ (mobiusTreeCheck_join cg 1200001 3 647168 _ _ (mobiusTreeCheck_join cg 1200001 2 647168 _ _ (mobiusTreeCheck_join cg 1200001 1 647168 _ _ p263 p264) (mobiusTreeCheck_join cg 1200001 1 647296 _ _ p266 p267)) (mobiusTreeCheck_join cg 1200001 2 647424 _ _ (mobiusTreeCheck_join cg 1200001 1 647424 _ _ p270 p271) (mobiusTreeCheck_join cg 1200001 1 647552 _ _ p273 p274))) (mobiusTreeCheck_join cg 1200001 3 647680 _ _ (mobiusTreeCheck_join cg 1200001 2 647680 _ _ (mobiusTreeCheck_join cg 1200001 1 647680 _ _ p278 p279) (mobiusTreeCheck_join cg 1200001 1 647808 _ _ p281 p282)) (mobiusTreeCheck_join cg 1200001 2 647936 _ _ (mobiusTreeCheck_join cg 1200001 1 647936 _ _ p285 p286) (mobiusTreeCheck_join cg 1200001 1 648064 _ _ p288 p289)))) (mobiusTreeCheck_join cg 1200001 4 648192 _ _ (mobiusTreeCheck_join cg 1200001 3 648192 _ _ (mobiusTreeCheck_join cg 1200001 2 648192 _ _ (mobiusTreeCheck_join cg 1200001 1 648192 _ _ p294 p295) (mobiusTreeCheck_join cg 1200001 1 648320 _ _ p297 p298)) (mobiusTreeCheck_join cg 1200001 2 648448 _ _ (mobiusTreeCheck_join cg 1200001 1 648448 _ _ p301 p302) (mobiusTreeCheck_join cg 1200001 1 648576 _ _ p304 p305))) (mobiusTreeCheck_join cg 1200001 3 648704 _ _ (mobiusTreeCheck_join cg 1200001 2 648704 _ _ (mobiusTreeCheck_join cg 1200001 1 648704 _ _ p309 p310) (mobiusTreeCheck_join cg 1200001 1 648832 _ _ p312 p313)) (mobiusTreeCheck_join cg 1200001 2 648960 _ _ (mobiusTreeCheck_join cg 1200001 1 648960 _ _ p316 p317) (mobiusTreeCheck_join cg 1200001 1 649088 _ _ p319 p320))))) (mobiusTreeCheck_join cg 1200001 5 649216 _ _ (mobiusTreeCheck_join cg 1200001 4 649216 _ _ (mobiusTreeCheck_join cg 1200001 3 649216 _ _ (mobiusTreeCheck_join cg 1200001 2 649216 _ _ (mobiusTreeCheck_join cg 1200001 1 649216 _ _ p326 p327) (mobiusTreeCheck_join cg 1200001 1 649344 _ _ p329 p330)) (mobiusTreeCheck_join cg 1200001 2 649472 _ _ (mobiusTreeCheck_join cg 1200001 1 649472 _ _ p333 p334) (mobiusTreeCheck_join cg 1200001 1 649600 _ _ p336 p337))) (mobiusTreeCheck_join cg 1200001 3 649728 _ _ (mobiusTreeCheck_join cg 1200001 2 649728 _ _ (mobiusTreeCheck_join cg 1200001 1 649728 _ _ p341 p342) (mobiusTreeCheck_join cg 1200001 1 649856 _ _ p344 p345)) (mobiusTreeCheck_join cg 1200001 2 649984 _ _ (mobiusTreeCheck_join cg 1200001 1 649984 _ _ p348 p349) (mobiusTreeCheck_join cg 1200001 1 650112 _ _ p351 p352)))) (mobiusTreeCheck_join cg 1200001 4 650240 _ _ (mobiusTreeCheck_join cg 1200001 3 650240 _ _ (mobiusTreeCheck_join cg 1200001 2 650240 _ _ (mobiusTreeCheck_join cg 1200001 1 650240 _ _ p357 p358) (mobiusTreeCheck_join cg 1200001 1 650368 _ _ p360 p361)) (mobiusTreeCheck_join cg 1200001 2 650496 _ _ (mobiusTreeCheck_join cg 1200001 1 650496 _ _ p364 p365) (mobiusTreeCheck_join cg 1200001 1 650624 _ _ p367 p368))) (mobiusTreeCheck_join cg 1200001 3 650752 _ _ (mobiusTreeCheck_join cg 1200001 2 650752 _ _ (mobiusTreeCheck_join cg 1200001 1 650752 _ _ p372 p373) (mobiusTreeCheck_join cg 1200001 1 650880 _ _ p375 p376)) (mobiusTreeCheck_join cg 1200001 2 651008 _ _ (mobiusTreeCheck_join cg 1200001 1 651008 _ _ p379 p380) (mobiusTreeCheck_join cg 1200001 1 651136 _ _ p382 p383)))))) (mobiusTreeCheck_join cg 1200001 6 651264 _ _ (mobiusTreeCheck_join cg 1200001 5 651264 _ _ (mobiusTreeCheck_join cg 1200001 4 651264 _ _ (mobiusTreeCheck_join cg 1200001 3 651264 _ _ (mobiusTreeCheck_join cg 1200001 2 651264 _ _ (mobiusTreeCheck_join cg 1200001 1 651264 _ _ p390 p391) (mobiusTreeCheck_join cg 1200001 1 651392 _ _ p393 p394)) (mobiusTreeCheck_join cg 1200001 2 651520 _ _ (mobiusTreeCheck_join cg 1200001 1 651520 _ _ p397 p398) (mobiusTreeCheck_join cg 1200001 1 651648 _ _ p400 p401))) (mobiusTreeCheck_join cg 1200001 3 651776 _ _ (mobiusTreeCheck_join cg 1200001 2 651776 _ _ (mobiusTreeCheck_join cg 1200001 1 651776 _ _ p405 p406) (mobiusTreeCheck_join cg 1200001 1 651904 _ _ p408 p409)) (mobiusTreeCheck_join cg 1200001 2 652032 _ _ (mobiusTreeCheck_join cg 1200001 1 652032 _ _ p412 p413) (mobiusTreeCheck_join cg 1200001 1 652160 _ _ p415 p416)))) (mobiusTreeCheck_join cg 1200001 4 652288 _ _ (mobiusTreeCheck_join cg 1200001 3 652288 _ _ (mobiusTreeCheck_join cg 1200001 2 652288 _ _ (mobiusTreeCheck_join cg 1200001 1 652288 _ _ p421 p422) (mobiusTreeCheck_join cg 1200001 1 652416 _ _ p424 p425)) (mobiusTreeCheck_join cg 1200001 2 652544 _ _ (mobiusTreeCheck_join cg 1200001 1 652544 _ _ p428 p429) (mobiusTreeCheck_join cg 1200001 1 652672 _ _ p431 p432))) (mobiusTreeCheck_join cg 1200001 3 652800 _ _ (mobiusTreeCheck_join cg 1200001 2 652800 _ _ (mobiusTreeCheck_join cg 1200001 1 652800 _ _ p436 p437) (mobiusTreeCheck_join cg 1200001 1 652928 _ _ p439 p440)) (mobiusTreeCheck_join cg 1200001 2 653056 _ _ (mobiusTreeCheck_join cg 1200001 1 653056 _ _ p443 p444) (mobiusTreeCheck_join cg 1200001 1 653184 _ _ p446 p447))))) (mobiusTreeCheck_join cg 1200001 5 653312 _ _ (mobiusTreeCheck_join cg 1200001 4 653312 _ _ (mobiusTreeCheck_join cg 1200001 3 653312 _ _ (mobiusTreeCheck_join cg 1200001 2 653312 _ _ (mobiusTreeCheck_join cg 1200001 1 653312 _ _ p453 p454) (mobiusTreeCheck_join cg 1200001 1 653440 _ _ p456 p457)) (mobiusTreeCheck_join cg 1200001 2 653568 _ _ (mobiusTreeCheck_join cg 1200001 1 653568 _ _ p460 p461) (mobiusTreeCheck_join cg 1200001 1 653696 _ _ p463 p464))) (mobiusTreeCheck_join cg 1200001 3 653824 _ _ (mobiusTreeCheck_join cg 1200001 2 653824 _ _ (mobiusTreeCheck_join cg 1200001 1 653824 _ _ p468 p469) (mobiusTreeCheck_join cg 1200001 1 653952 _ _ p471 p472)) (mobiusTreeCheck_join cg 1200001 2 654080 _ _ (mobiusTreeCheck_join cg 1200001 1 654080 _ _ p475 p476) (mobiusTreeCheck_join cg 1200001 1 654208 _ _ p478 p479)))) (mobiusTreeCheck_join cg 1200001 4 654336 _ _ (mobiusTreeCheck_join cg 1200001 3 654336 _ _ (mobiusTreeCheck_join cg 1200001 2 654336 _ _ (mobiusTreeCheck_join cg 1200001 1 654336 _ _ p484 p485) (mobiusTreeCheck_join cg 1200001 1 654464 _ _ p487 p488)) (mobiusTreeCheck_join cg 1200001 2 654592 _ _ (mobiusTreeCheck_join cg 1200001 1 654592 _ _ p491 p492) (mobiusTreeCheck_join cg 1200001 1 654720 _ _ p494 p495))) (mobiusTreeCheck_join cg 1200001 3 654848 _ _ (mobiusTreeCheck_join cg 1200001 2 654848 _ _ (mobiusTreeCheck_join cg 1200001 1 654848 _ _ p499 p500) (mobiusTreeCheck_join cg 1200001 1 654976 _ _ p502 p503)) (mobiusTreeCheck_join cg 1200001 2 655104 _ _ (mobiusTreeCheck_join cg 1200001 1 655104 _ _ p506 p507) (mobiusTreeCheck_join cg 1200001 1 655232 _ _ p509 p510))))))))

end Helfgott

open Helfgott
theorem solution : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 638976 (MobiusCertTree.branch mobiusTableBlock078 mobiusTableBlock079) = true := Helfgott.combined

#print axioms solution
