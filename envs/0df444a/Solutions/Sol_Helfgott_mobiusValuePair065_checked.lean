-- Prove2me | solution 1 for Helfgott.mobiusValuePair065_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:53:12.274964+00:00
-- url     : https://prove2.me/submissions/474a8932-930c-4d0f-80f7-820dbd0da550

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

private abbrev d8 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 0
private theorem p8 : mobiusTreeCheck cg 1200001 1 1064960 d8 = true := by decide +kernel

private abbrev d9 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 1
private theorem p9 : mobiusTreeCheck cg 1200001 1 1065024 d9 = true := by decide +kernel

private def d7 : MobiusCertTree := .branch d8 d9
private abbrev d11 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 2
private theorem p11 : mobiusTreeCheck cg 1200001 1 1065088 d11 = true := by decide +kernel

private abbrev d12 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 3
private theorem p12 : mobiusTreeCheck cg 1200001 1 1065152 d12 = true := by decide +kernel

private def d10 : MobiusCertTree := .branch d11 d12
private def d6 : MobiusCertTree := .branch d7 d10
private abbrev d15 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 4
private theorem p15 : mobiusTreeCheck cg 1200001 1 1065216 d15 = true := by decide +kernel

private abbrev d16 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 5
private theorem p16 : mobiusTreeCheck cg 1200001 1 1065280 d16 = true := by decide +kernel

private def d14 : MobiusCertTree := .branch d15 d16
private abbrev d18 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 6
private theorem p18 : mobiusTreeCheck cg 1200001 1 1065344 d18 = true := by decide +kernel

private abbrev d19 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 7
private theorem p19 : mobiusTreeCheck cg 1200001 1 1065408 d19 = true := by decide +kernel

private def d17 : MobiusCertTree := .branch d18 d19
private def d13 : MobiusCertTree := .branch d14 d17
private def d5 : MobiusCertTree := .branch d6 d13
private abbrev d23 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 8
private theorem p23 : mobiusTreeCheck cg 1200001 1 1065472 d23 = true := by decide +kernel

private abbrev d24 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 9
private theorem p24 : mobiusTreeCheck cg 1200001 1 1065536 d24 = true := by decide +kernel

private def d22 : MobiusCertTree := .branch d23 d24
private abbrev d26 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 10
private theorem p26 : mobiusTreeCheck cg 1200001 1 1065600 d26 = true := by decide +kernel

private abbrev d27 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 11
private theorem p27 : mobiusTreeCheck cg 1200001 1 1065664 d27 = true := by decide +kernel

private def d25 : MobiusCertTree := .branch d26 d27
private def d21 : MobiusCertTree := .branch d22 d25
private abbrev d30 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 12
private theorem p30 : mobiusTreeCheck cg 1200001 1 1065728 d30 = true := by decide +kernel

private abbrev d31 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 13
private theorem p31 : mobiusTreeCheck cg 1200001 1 1065792 d31 = true := by decide +kernel

private def d29 : MobiusCertTree := .branch d30 d31
private abbrev d33 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 14
private theorem p33 : mobiusTreeCheck cg 1200001 1 1065856 d33 = true := by decide +kernel

private abbrev d34 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 15
private theorem p34 : mobiusTreeCheck cg 1200001 1 1065920 d34 = true := by decide +kernel

private def d32 : MobiusCertTree := .branch d33 d34
private def d28 : MobiusCertTree := .branch d29 d32
private def d20 : MobiusCertTree := .branch d21 d28
private def d4 : MobiusCertTree := .branch d5 d20
private abbrev d39 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 16
private theorem p39 : mobiusTreeCheck cg 1200001 1 1065984 d39 = true := by decide +kernel

private abbrev d40 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 17
private theorem p40 : mobiusTreeCheck cg 1200001 1 1066048 d40 = true := by decide +kernel

private def d38 : MobiusCertTree := .branch d39 d40
private abbrev d42 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 18
private theorem p42 : mobiusTreeCheck cg 1200001 1 1066112 d42 = true := by decide +kernel

private abbrev d43 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 19
private theorem p43 : mobiusTreeCheck cg 1200001 1 1066176 d43 = true := by decide +kernel

private def d41 : MobiusCertTree := .branch d42 d43
private def d37 : MobiusCertTree := .branch d38 d41
private abbrev d46 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 20
private theorem p46 : mobiusTreeCheck cg 1200001 1 1066240 d46 = true := by decide +kernel

private abbrev d47 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 21
private theorem p47 : mobiusTreeCheck cg 1200001 1 1066304 d47 = true := by decide +kernel

private def d45 : MobiusCertTree := .branch d46 d47
private abbrev d49 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 22
private theorem p49 : mobiusTreeCheck cg 1200001 1 1066368 d49 = true := by decide +kernel

private abbrev d50 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 23
private theorem p50 : mobiusTreeCheck cg 1200001 1 1066432 d50 = true := by decide +kernel

private def d48 : MobiusCertTree := .branch d49 d50
private def d44 : MobiusCertTree := .branch d45 d48
private def d36 : MobiusCertTree := .branch d37 d44
private abbrev d54 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 24
private theorem p54 : mobiusTreeCheck cg 1200001 1 1066496 d54 = true := by decide +kernel

private abbrev d55 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 25
private theorem p55 : mobiusTreeCheck cg 1200001 1 1066560 d55 = true := by decide +kernel

private def d53 : MobiusCertTree := .branch d54 d55
private abbrev d57 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 26
private theorem p57 : mobiusTreeCheck cg 1200001 1 1066624 d57 = true := by decide +kernel

private abbrev d58 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 27
private theorem p58 : mobiusTreeCheck cg 1200001 1 1066688 d58 = true := by decide +kernel

private def d56 : MobiusCertTree := .branch d57 d58
private def d52 : MobiusCertTree := .branch d53 d56
private abbrev d61 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 28
private theorem p61 : mobiusTreeCheck cg 1200001 1 1066752 d61 = true := by decide +kernel

private abbrev d62 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 29
private theorem p62 : mobiusTreeCheck cg 1200001 1 1066816 d62 = true := by decide +kernel

private def d60 : MobiusCertTree := .branch d61 d62
private abbrev d64 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 30
private theorem p64 : mobiusTreeCheck cg 1200001 1 1066880 d64 = true := by decide +kernel

private abbrev d65 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 31
private theorem p65 : mobiusTreeCheck cg 1200001 1 1066944 d65 = true := by decide +kernel

private def d63 : MobiusCertTree := .branch d64 d65
private def d59 : MobiusCertTree := .branch d60 d63
private def d51 : MobiusCertTree := .branch d52 d59
private def d35 : MobiusCertTree := .branch d36 d51
private def d3 : MobiusCertTree := .branch d4 d35
private abbrev d71 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 32
private theorem p71 : mobiusTreeCheck cg 1200001 1 1067008 d71 = true := by decide +kernel

private abbrev d72 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 33
private theorem p72 : mobiusTreeCheck cg 1200001 1 1067072 d72 = true := by decide +kernel

private def d70 : MobiusCertTree := .branch d71 d72
private abbrev d74 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 34
private theorem p74 : mobiusTreeCheck cg 1200001 1 1067136 d74 = true := by decide +kernel

private abbrev d75 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 35
private theorem p75 : mobiusTreeCheck cg 1200001 1 1067200 d75 = true := by decide +kernel

private def d73 : MobiusCertTree := .branch d74 d75
private def d69 : MobiusCertTree := .branch d70 d73
private abbrev d78 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 36
private theorem p78 : mobiusTreeCheck cg 1200001 1 1067264 d78 = true := by decide +kernel

private abbrev d79 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 37
private theorem p79 : mobiusTreeCheck cg 1200001 1 1067328 d79 = true := by decide +kernel

private def d77 : MobiusCertTree := .branch d78 d79
private abbrev d81 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 38
private theorem p81 : mobiusTreeCheck cg 1200001 1 1067392 d81 = true := by decide +kernel

private abbrev d82 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 39
private theorem p82 : mobiusTreeCheck cg 1200001 1 1067456 d82 = true := by decide +kernel

private def d80 : MobiusCertTree := .branch d81 d82
private def d76 : MobiusCertTree := .branch d77 d80
private def d68 : MobiusCertTree := .branch d69 d76
private abbrev d86 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 40
private theorem p86 : mobiusTreeCheck cg 1200001 1 1067520 d86 = true := by decide +kernel

private abbrev d87 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 41
private theorem p87 : mobiusTreeCheck cg 1200001 1 1067584 d87 = true := by decide +kernel

private def d85 : MobiusCertTree := .branch d86 d87
private abbrev d89 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 42
private theorem p89 : mobiusTreeCheck cg 1200001 1 1067648 d89 = true := by decide +kernel

private abbrev d90 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 43
private theorem p90 : mobiusTreeCheck cg 1200001 1 1067712 d90 = true := by decide +kernel

private def d88 : MobiusCertTree := .branch d89 d90
private def d84 : MobiusCertTree := .branch d85 d88
private abbrev d93 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 44
private theorem p93 : mobiusTreeCheck cg 1200001 1 1067776 d93 = true := by decide +kernel

private abbrev d94 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 45
private theorem p94 : mobiusTreeCheck cg 1200001 1 1067840 d94 = true := by decide +kernel

private def d92 : MobiusCertTree := .branch d93 d94
private abbrev d96 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 46
private theorem p96 : mobiusTreeCheck cg 1200001 1 1067904 d96 = true := by decide +kernel

private abbrev d97 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 47
private theorem p97 : mobiusTreeCheck cg 1200001 1 1067968 d97 = true := by decide +kernel

private def d95 : MobiusCertTree := .branch d96 d97
private def d91 : MobiusCertTree := .branch d92 d95
private def d83 : MobiusCertTree := .branch d84 d91
private def d67 : MobiusCertTree := .branch d68 d83
private abbrev d102 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 48
private theorem p102 : mobiusTreeCheck cg 1200001 1 1068032 d102 = true := by decide +kernel

private abbrev d103 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 49
private theorem p103 : mobiusTreeCheck cg 1200001 1 1068096 d103 = true := by decide +kernel

private def d101 : MobiusCertTree := .branch d102 d103
private abbrev d105 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 50
private theorem p105 : mobiusTreeCheck cg 1200001 1 1068160 d105 = true := by decide +kernel

private abbrev d106 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 51
private theorem p106 : mobiusTreeCheck cg 1200001 1 1068224 d106 = true := by decide +kernel

private def d104 : MobiusCertTree := .branch d105 d106
private def d100 : MobiusCertTree := .branch d101 d104
private abbrev d109 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 52
private theorem p109 : mobiusTreeCheck cg 1200001 1 1068288 d109 = true := by decide +kernel

private abbrev d110 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 53
private theorem p110 : mobiusTreeCheck cg 1200001 1 1068352 d110 = true := by decide +kernel

private def d108 : MobiusCertTree := .branch d109 d110
private abbrev d112 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 54
private theorem p112 : mobiusTreeCheck cg 1200001 1 1068416 d112 = true := by decide +kernel

private abbrev d113 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 55
private theorem p113 : mobiusTreeCheck cg 1200001 1 1068480 d113 = true := by decide +kernel

private def d111 : MobiusCertTree := .branch d112 d113
private def d107 : MobiusCertTree := .branch d108 d111
private def d99 : MobiusCertTree := .branch d100 d107
private abbrev d117 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 56
private theorem p117 : mobiusTreeCheck cg 1200001 1 1068544 d117 = true := by decide +kernel

private abbrev d118 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 57
private theorem p118 : mobiusTreeCheck cg 1200001 1 1068608 d118 = true := by decide +kernel

private def d116 : MobiusCertTree := .branch d117 d118
private abbrev d120 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 58
private theorem p120 : mobiusTreeCheck cg 1200001 1 1068672 d120 = true := by decide +kernel

private abbrev d121 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 59
private theorem p121 : mobiusTreeCheck cg 1200001 1 1068736 d121 = true := by decide +kernel

private def d119 : MobiusCertTree := .branch d120 d121
private def d115 : MobiusCertTree := .branch d116 d119
private abbrev d124 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 60
private theorem p124 : mobiusTreeCheck cg 1200001 1 1068800 d124 = true := by decide +kernel

private abbrev d125 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 61
private theorem p125 : mobiusTreeCheck cg 1200001 1 1068864 d125 = true := by decide +kernel

private def d123 : MobiusCertTree := .branch d124 d125
private abbrev d127 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 62
private theorem p127 : mobiusTreeCheck cg 1200001 1 1068928 d127 = true := by decide +kernel

private abbrev d128 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 63
private theorem p128 : mobiusTreeCheck cg 1200001 1 1068992 d128 = true := by decide +kernel

private def d126 : MobiusCertTree := .branch d127 d128
private def d122 : MobiusCertTree := .branch d123 d126
private def d114 : MobiusCertTree := .branch d115 d122
private def d98 : MobiusCertTree := .branch d99 d114
private def d66 : MobiusCertTree := .branch d67 d98
private def d2 : MobiusCertTree := .branch d3 d66
private abbrev d135 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 64
private theorem p135 : mobiusTreeCheck cg 1200001 1 1069056 d135 = true := by decide +kernel

private abbrev d136 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 65
private theorem p136 : mobiusTreeCheck cg 1200001 1 1069120 d136 = true := by decide +kernel

private def d134 : MobiusCertTree := .branch d135 d136
private abbrev d138 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 66
private theorem p138 : mobiusTreeCheck cg 1200001 1 1069184 d138 = true := by decide +kernel

private abbrev d139 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 67
private theorem p139 : mobiusTreeCheck cg 1200001 1 1069248 d139 = true := by decide +kernel

private def d137 : MobiusCertTree := .branch d138 d139
private def d133 : MobiusCertTree := .branch d134 d137
private abbrev d142 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 68
private theorem p142 : mobiusTreeCheck cg 1200001 1 1069312 d142 = true := by decide +kernel

private abbrev d143 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 69
private theorem p143 : mobiusTreeCheck cg 1200001 1 1069376 d143 = true := by decide +kernel

private def d141 : MobiusCertTree := .branch d142 d143
private abbrev d145 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 70
private theorem p145 : mobiusTreeCheck cg 1200001 1 1069440 d145 = true := by decide +kernel

private abbrev d146 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 71
private theorem p146 : mobiusTreeCheck cg 1200001 1 1069504 d146 = true := by decide +kernel

private def d144 : MobiusCertTree := .branch d145 d146
private def d140 : MobiusCertTree := .branch d141 d144
private def d132 : MobiusCertTree := .branch d133 d140
private abbrev d150 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 72
private theorem p150 : mobiusTreeCheck cg 1200001 1 1069568 d150 = true := by decide +kernel

private abbrev d151 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 73
private theorem p151 : mobiusTreeCheck cg 1200001 1 1069632 d151 = true := by decide +kernel

private def d149 : MobiusCertTree := .branch d150 d151
private abbrev d153 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 74
private theorem p153 : mobiusTreeCheck cg 1200001 1 1069696 d153 = true := by decide +kernel

private abbrev d154 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 75
private theorem p154 : mobiusTreeCheck cg 1200001 1 1069760 d154 = true := by decide +kernel

private def d152 : MobiusCertTree := .branch d153 d154
private def d148 : MobiusCertTree := .branch d149 d152
private abbrev d157 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 76
private theorem p157 : mobiusTreeCheck cg 1200001 1 1069824 d157 = true := by decide +kernel

private abbrev d158 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 77
private theorem p158 : mobiusTreeCheck cg 1200001 1 1069888 d158 = true := by decide +kernel

private def d156 : MobiusCertTree := .branch d157 d158
private abbrev d160 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 78
private theorem p160 : mobiusTreeCheck cg 1200001 1 1069952 d160 = true := by decide +kernel

private abbrev d161 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 79
private theorem p161 : mobiusTreeCheck cg 1200001 1 1070016 d161 = true := by decide +kernel

private def d159 : MobiusCertTree := .branch d160 d161
private def d155 : MobiusCertTree := .branch d156 d159
private def d147 : MobiusCertTree := .branch d148 d155
private def d131 : MobiusCertTree := .branch d132 d147
private abbrev d166 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 80
private theorem p166 : mobiusTreeCheck cg 1200001 1 1070080 d166 = true := by decide +kernel

private abbrev d167 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 81
private theorem p167 : mobiusTreeCheck cg 1200001 1 1070144 d167 = true := by decide +kernel

private def d165 : MobiusCertTree := .branch d166 d167
private abbrev d169 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 82
private theorem p169 : mobiusTreeCheck cg 1200001 1 1070208 d169 = true := by decide +kernel

private abbrev d170 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 83
private theorem p170 : mobiusTreeCheck cg 1200001 1 1070272 d170 = true := by decide +kernel

private def d168 : MobiusCertTree := .branch d169 d170
private def d164 : MobiusCertTree := .branch d165 d168
private abbrev d173 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 84
private theorem p173 : mobiusTreeCheck cg 1200001 1 1070336 d173 = true := by decide +kernel

private abbrev d174 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 85
private theorem p174 : mobiusTreeCheck cg 1200001 1 1070400 d174 = true := by decide +kernel

private def d172 : MobiusCertTree := .branch d173 d174
private abbrev d176 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 86
private theorem p176 : mobiusTreeCheck cg 1200001 1 1070464 d176 = true := by decide +kernel

private abbrev d177 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 87
private theorem p177 : mobiusTreeCheck cg 1200001 1 1070528 d177 = true := by decide +kernel

private def d175 : MobiusCertTree := .branch d176 d177
private def d171 : MobiusCertTree := .branch d172 d175
private def d163 : MobiusCertTree := .branch d164 d171
private abbrev d181 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 88
private theorem p181 : mobiusTreeCheck cg 1200001 1 1070592 d181 = true := by decide +kernel

private abbrev d182 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 89
private theorem p182 : mobiusTreeCheck cg 1200001 1 1070656 d182 = true := by decide +kernel

private def d180 : MobiusCertTree := .branch d181 d182
private abbrev d184 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 90
private theorem p184 : mobiusTreeCheck cg 1200001 1 1070720 d184 = true := by decide +kernel

private abbrev d185 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 91
private theorem p185 : mobiusTreeCheck cg 1200001 1 1070784 d185 = true := by decide +kernel

private def d183 : MobiusCertTree := .branch d184 d185
private def d179 : MobiusCertTree := .branch d180 d183
private abbrev d188 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 92
private theorem p188 : mobiusTreeCheck cg 1200001 1 1070848 d188 = true := by decide +kernel

private abbrev d189 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 93
private theorem p189 : mobiusTreeCheck cg 1200001 1 1070912 d189 = true := by decide +kernel

private def d187 : MobiusCertTree := .branch d188 d189
private abbrev d191 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 94
private theorem p191 : mobiusTreeCheck cg 1200001 1 1070976 d191 = true := by decide +kernel

private abbrev d192 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 95
private theorem p192 : mobiusTreeCheck cg 1200001 1 1071040 d192 = true := by decide +kernel

private def d190 : MobiusCertTree := .branch d191 d192
private def d186 : MobiusCertTree := .branch d187 d190
private def d178 : MobiusCertTree := .branch d179 d186
private def d162 : MobiusCertTree := .branch d163 d178
private def d130 : MobiusCertTree := .branch d131 d162
private abbrev d198 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 96
private theorem p198 : mobiusTreeCheck cg 1200001 1 1071104 d198 = true := by decide +kernel

private abbrev d199 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 97
private theorem p199 : mobiusTreeCheck cg 1200001 1 1071168 d199 = true := by decide +kernel

private def d197 : MobiusCertTree := .branch d198 d199
private abbrev d201 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 98
private theorem p201 : mobiusTreeCheck cg 1200001 1 1071232 d201 = true := by decide +kernel

private abbrev d202 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 99
private theorem p202 : mobiusTreeCheck cg 1200001 1 1071296 d202 = true := by decide +kernel

private def d200 : MobiusCertTree := .branch d201 d202
private def d196 : MobiusCertTree := .branch d197 d200
private abbrev d205 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 100
private theorem p205 : mobiusTreeCheck cg 1200001 1 1071360 d205 = true := by decide +kernel

private abbrev d206 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 101
private theorem p206 : mobiusTreeCheck cg 1200001 1 1071424 d206 = true := by decide +kernel

private def d204 : MobiusCertTree := .branch d205 d206
private abbrev d208 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 102
private theorem p208 : mobiusTreeCheck cg 1200001 1 1071488 d208 = true := by decide +kernel

private abbrev d209 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 103
private theorem p209 : mobiusTreeCheck cg 1200001 1 1071552 d209 = true := by decide +kernel

private def d207 : MobiusCertTree := .branch d208 d209
private def d203 : MobiusCertTree := .branch d204 d207
private def d195 : MobiusCertTree := .branch d196 d203
private abbrev d213 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 104
private theorem p213 : mobiusTreeCheck cg 1200001 1 1071616 d213 = true := by decide +kernel

private abbrev d214 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 105
private theorem p214 : mobiusTreeCheck cg 1200001 1 1071680 d214 = true := by decide +kernel

private def d212 : MobiusCertTree := .branch d213 d214
private abbrev d216 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 106
private theorem p216 : mobiusTreeCheck cg 1200001 1 1071744 d216 = true := by decide +kernel

private abbrev d217 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 107
private theorem p217 : mobiusTreeCheck cg 1200001 1 1071808 d217 = true := by decide +kernel

private def d215 : MobiusCertTree := .branch d216 d217
private def d211 : MobiusCertTree := .branch d212 d215
private abbrev d220 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 108
private theorem p220 : mobiusTreeCheck cg 1200001 1 1071872 d220 = true := by decide +kernel

private abbrev d221 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 109
private theorem p221 : mobiusTreeCheck cg 1200001 1 1071936 d221 = true := by decide +kernel

private def d219 : MobiusCertTree := .branch d220 d221
private abbrev d223 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 110
private theorem p223 : mobiusTreeCheck cg 1200001 1 1072000 d223 = true := by decide +kernel

private abbrev d224 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 111
private theorem p224 : mobiusTreeCheck cg 1200001 1 1072064 d224 = true := by decide +kernel

private def d222 : MobiusCertTree := .branch d223 d224
private def d218 : MobiusCertTree := .branch d219 d222
private def d210 : MobiusCertTree := .branch d211 d218
private def d194 : MobiusCertTree := .branch d195 d210
private abbrev d229 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 112
private theorem p229 : mobiusTreeCheck cg 1200001 1 1072128 d229 = true := by decide +kernel

private abbrev d230 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 113
private theorem p230 : mobiusTreeCheck cg 1200001 1 1072192 d230 = true := by decide +kernel

private def d228 : MobiusCertTree := .branch d229 d230
private abbrev d232 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 114
private theorem p232 : mobiusTreeCheck cg 1200001 1 1072256 d232 = true := by decide +kernel

private abbrev d233 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 115
private theorem p233 : mobiusTreeCheck cg 1200001 1 1072320 d233 = true := by decide +kernel

private def d231 : MobiusCertTree := .branch d232 d233
private def d227 : MobiusCertTree := .branch d228 d231
private abbrev d236 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 116
private theorem p236 : mobiusTreeCheck cg 1200001 1 1072384 d236 = true := by decide +kernel

private abbrev d237 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 117
private theorem p237 : mobiusTreeCheck cg 1200001 1 1072448 d237 = true := by decide +kernel

private def d235 : MobiusCertTree := .branch d236 d237
private abbrev d239 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 118
private theorem p239 : mobiusTreeCheck cg 1200001 1 1072512 d239 = true := by decide +kernel

private abbrev d240 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 119
private theorem p240 : mobiusTreeCheck cg 1200001 1 1072576 d240 = true := by decide +kernel

private def d238 : MobiusCertTree := .branch d239 d240
private def d234 : MobiusCertTree := .branch d235 d238
private def d226 : MobiusCertTree := .branch d227 d234
private abbrev d244 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 120
private theorem p244 : mobiusTreeCheck cg 1200001 1 1072640 d244 = true := by decide +kernel

private abbrev d245 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 121
private theorem p245 : mobiusTreeCheck cg 1200001 1 1072704 d245 = true := by decide +kernel

private def d243 : MobiusCertTree := .branch d244 d245
private abbrev d247 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 122
private theorem p247 : mobiusTreeCheck cg 1200001 1 1072768 d247 = true := by decide +kernel

private abbrev d248 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 123
private theorem p248 : mobiusTreeCheck cg 1200001 1 1072832 d248 = true := by decide +kernel

private def d246 : MobiusCertTree := .branch d247 d248
private def d242 : MobiusCertTree := .branch d243 d246
private abbrev d251 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 124
private theorem p251 : mobiusTreeCheck cg 1200001 1 1072896 d251 = true := by decide +kernel

private abbrev d252 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 125
private theorem p252 : mobiusTreeCheck cg 1200001 1 1072960 d252 = true := by decide +kernel

private def d250 : MobiusCertTree := .branch d251 d252
private abbrev d254 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 126
private theorem p254 : mobiusTreeCheck cg 1200001 1 1073024 d254 = true := by decide +kernel

private abbrev d255 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock130 127
private theorem p255 : mobiusTreeCheck cg 1200001 1 1073088 d255 = true := by decide +kernel

private def d253 : MobiusCertTree := .branch d254 d255
private def d249 : MobiusCertTree := .branch d250 d253
private def d241 : MobiusCertTree := .branch d242 d249
private def d225 : MobiusCertTree := .branch d226 d241
private def d193 : MobiusCertTree := .branch d194 d225
private def d129 : MobiusCertTree := .branch d130 d193
private def d1 : MobiusCertTree := .branch d2 d129
private abbrev d263 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 0
private theorem p263 : mobiusTreeCheck cg 1200001 1 1073152 d263 = true := by decide +kernel

private abbrev d264 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 1
private theorem p264 : mobiusTreeCheck cg 1200001 1 1073216 d264 = true := by decide +kernel

private def d262 : MobiusCertTree := .branch d263 d264
private abbrev d266 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 2
private theorem p266 : mobiusTreeCheck cg 1200001 1 1073280 d266 = true := by decide +kernel

private abbrev d267 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 3
private theorem p267 : mobiusTreeCheck cg 1200001 1 1073344 d267 = true := by decide +kernel

private def d265 : MobiusCertTree := .branch d266 d267
private def d261 : MobiusCertTree := .branch d262 d265
private abbrev d270 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 4
private theorem p270 : mobiusTreeCheck cg 1200001 1 1073408 d270 = true := by decide +kernel

private abbrev d271 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 5
private theorem p271 : mobiusTreeCheck cg 1200001 1 1073472 d271 = true := by decide +kernel

private def d269 : MobiusCertTree := .branch d270 d271
private abbrev d273 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 6
private theorem p273 : mobiusTreeCheck cg 1200001 1 1073536 d273 = true := by decide +kernel

private abbrev d274 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 7
private theorem p274 : mobiusTreeCheck cg 1200001 1 1073600 d274 = true := by decide +kernel

private def d272 : MobiusCertTree := .branch d273 d274
private def d268 : MobiusCertTree := .branch d269 d272
private def d260 : MobiusCertTree := .branch d261 d268
private abbrev d278 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 8
private theorem p278 : mobiusTreeCheck cg 1200001 1 1073664 d278 = true := by decide +kernel

private abbrev d279 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 9
private theorem p279 : mobiusTreeCheck cg 1200001 1 1073728 d279 = true := by decide +kernel

private def d277 : MobiusCertTree := .branch d278 d279
private abbrev d281 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 10
private theorem p281 : mobiusTreeCheck cg 1200001 1 1073792 d281 = true := by decide +kernel

private abbrev d282 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 11
private theorem p282 : mobiusTreeCheck cg 1200001 1 1073856 d282 = true := by decide +kernel

private def d280 : MobiusCertTree := .branch d281 d282
private def d276 : MobiusCertTree := .branch d277 d280
private abbrev d285 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 12
private theorem p285 : mobiusTreeCheck cg 1200001 1 1073920 d285 = true := by decide +kernel

private abbrev d286 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 13
private theorem p286 : mobiusTreeCheck cg 1200001 1 1073984 d286 = true := by decide +kernel

private def d284 : MobiusCertTree := .branch d285 d286
private abbrev d288 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 14
private theorem p288 : mobiusTreeCheck cg 1200001 1 1074048 d288 = true := by decide +kernel

private abbrev d289 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 15
private theorem p289 : mobiusTreeCheck cg 1200001 1 1074112 d289 = true := by decide +kernel

private def d287 : MobiusCertTree := .branch d288 d289
private def d283 : MobiusCertTree := .branch d284 d287
private def d275 : MobiusCertTree := .branch d276 d283
private def d259 : MobiusCertTree := .branch d260 d275
private abbrev d294 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 16
private theorem p294 : mobiusTreeCheck cg 1200001 1 1074176 d294 = true := by decide +kernel

private abbrev d295 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 17
private theorem p295 : mobiusTreeCheck cg 1200001 1 1074240 d295 = true := by decide +kernel

private def d293 : MobiusCertTree := .branch d294 d295
private abbrev d297 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 18
private theorem p297 : mobiusTreeCheck cg 1200001 1 1074304 d297 = true := by decide +kernel

private abbrev d298 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 19
private theorem p298 : mobiusTreeCheck cg 1200001 1 1074368 d298 = true := by decide +kernel

private def d296 : MobiusCertTree := .branch d297 d298
private def d292 : MobiusCertTree := .branch d293 d296
private abbrev d301 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 20
private theorem p301 : mobiusTreeCheck cg 1200001 1 1074432 d301 = true := by decide +kernel

private abbrev d302 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 21
private theorem p302 : mobiusTreeCheck cg 1200001 1 1074496 d302 = true := by decide +kernel

private def d300 : MobiusCertTree := .branch d301 d302
private abbrev d304 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 22
private theorem p304 : mobiusTreeCheck cg 1200001 1 1074560 d304 = true := by decide +kernel

private abbrev d305 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 23
private theorem p305 : mobiusTreeCheck cg 1200001 1 1074624 d305 = true := by decide +kernel

private def d303 : MobiusCertTree := .branch d304 d305
private def d299 : MobiusCertTree := .branch d300 d303
private def d291 : MobiusCertTree := .branch d292 d299
private abbrev d309 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 24
private theorem p309 : mobiusTreeCheck cg 1200001 1 1074688 d309 = true := by decide +kernel

private abbrev d310 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 25
private theorem p310 : mobiusTreeCheck cg 1200001 1 1074752 d310 = true := by decide +kernel

private def d308 : MobiusCertTree := .branch d309 d310
private abbrev d312 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 26
private theorem p312 : mobiusTreeCheck cg 1200001 1 1074816 d312 = true := by decide +kernel

private abbrev d313 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 27
private theorem p313 : mobiusTreeCheck cg 1200001 1 1074880 d313 = true := by decide +kernel

private def d311 : MobiusCertTree := .branch d312 d313
private def d307 : MobiusCertTree := .branch d308 d311
private abbrev d316 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 28
private theorem p316 : mobiusTreeCheck cg 1200001 1 1074944 d316 = true := by decide +kernel

private abbrev d317 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 29
private theorem p317 : mobiusTreeCheck cg 1200001 1 1075008 d317 = true := by decide +kernel

private def d315 : MobiusCertTree := .branch d316 d317
private abbrev d319 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 30
private theorem p319 : mobiusTreeCheck cg 1200001 1 1075072 d319 = true := by decide +kernel

private abbrev d320 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 31
private theorem p320 : mobiusTreeCheck cg 1200001 1 1075136 d320 = true := by decide +kernel

private def d318 : MobiusCertTree := .branch d319 d320
private def d314 : MobiusCertTree := .branch d315 d318
private def d306 : MobiusCertTree := .branch d307 d314
private def d290 : MobiusCertTree := .branch d291 d306
private def d258 : MobiusCertTree := .branch d259 d290
private abbrev d326 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 32
private theorem p326 : mobiusTreeCheck cg 1200001 1 1075200 d326 = true := by decide +kernel

private abbrev d327 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 33
private theorem p327 : mobiusTreeCheck cg 1200001 1 1075264 d327 = true := by decide +kernel

private def d325 : MobiusCertTree := .branch d326 d327
private abbrev d329 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 34
private theorem p329 : mobiusTreeCheck cg 1200001 1 1075328 d329 = true := by decide +kernel

private abbrev d330 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 35
private theorem p330 : mobiusTreeCheck cg 1200001 1 1075392 d330 = true := by decide +kernel

private def d328 : MobiusCertTree := .branch d329 d330
private def d324 : MobiusCertTree := .branch d325 d328
private abbrev d333 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 36
private theorem p333 : mobiusTreeCheck cg 1200001 1 1075456 d333 = true := by decide +kernel

private abbrev d334 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 37
private theorem p334 : mobiusTreeCheck cg 1200001 1 1075520 d334 = true := by decide +kernel

private def d332 : MobiusCertTree := .branch d333 d334
private abbrev d336 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 38
private theorem p336 : mobiusTreeCheck cg 1200001 1 1075584 d336 = true := by decide +kernel

private abbrev d337 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 39
private theorem p337 : mobiusTreeCheck cg 1200001 1 1075648 d337 = true := by decide +kernel

private def d335 : MobiusCertTree := .branch d336 d337
private def d331 : MobiusCertTree := .branch d332 d335
private def d323 : MobiusCertTree := .branch d324 d331
private abbrev d341 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 40
private theorem p341 : mobiusTreeCheck cg 1200001 1 1075712 d341 = true := by decide +kernel

private abbrev d342 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 41
private theorem p342 : mobiusTreeCheck cg 1200001 1 1075776 d342 = true := by decide +kernel

private def d340 : MobiusCertTree := .branch d341 d342
private abbrev d344 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 42
private theorem p344 : mobiusTreeCheck cg 1200001 1 1075840 d344 = true := by decide +kernel

private abbrev d345 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 43
private theorem p345 : mobiusTreeCheck cg 1200001 1 1075904 d345 = true := by decide +kernel

private def d343 : MobiusCertTree := .branch d344 d345
private def d339 : MobiusCertTree := .branch d340 d343
private abbrev d348 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 44
private theorem p348 : mobiusTreeCheck cg 1200001 1 1075968 d348 = true := by decide +kernel

private abbrev d349 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 45
private theorem p349 : mobiusTreeCheck cg 1200001 1 1076032 d349 = true := by decide +kernel

private def d347 : MobiusCertTree := .branch d348 d349
private abbrev d351 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 46
private theorem p351 : mobiusTreeCheck cg 1200001 1 1076096 d351 = true := by decide +kernel

private abbrev d352 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 47
private theorem p352 : mobiusTreeCheck cg 1200001 1 1076160 d352 = true := by decide +kernel

private def d350 : MobiusCertTree := .branch d351 d352
private def d346 : MobiusCertTree := .branch d347 d350
private def d338 : MobiusCertTree := .branch d339 d346
private def d322 : MobiusCertTree := .branch d323 d338
private abbrev d357 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 48
private theorem p357 : mobiusTreeCheck cg 1200001 1 1076224 d357 = true := by decide +kernel

private abbrev d358 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 49
private theorem p358 : mobiusTreeCheck cg 1200001 1 1076288 d358 = true := by decide +kernel

private def d356 : MobiusCertTree := .branch d357 d358
private abbrev d360 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 50
private theorem p360 : mobiusTreeCheck cg 1200001 1 1076352 d360 = true := by decide +kernel

private abbrev d361 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 51
private theorem p361 : mobiusTreeCheck cg 1200001 1 1076416 d361 = true := by decide +kernel

private def d359 : MobiusCertTree := .branch d360 d361
private def d355 : MobiusCertTree := .branch d356 d359
private abbrev d364 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 52
private theorem p364 : mobiusTreeCheck cg 1200001 1 1076480 d364 = true := by decide +kernel

private abbrev d365 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 53
private theorem p365 : mobiusTreeCheck cg 1200001 1 1076544 d365 = true := by decide +kernel

private def d363 : MobiusCertTree := .branch d364 d365
private abbrev d367 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 54
private theorem p367 : mobiusTreeCheck cg 1200001 1 1076608 d367 = true := by decide +kernel

private abbrev d368 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 55
private theorem p368 : mobiusTreeCheck cg 1200001 1 1076672 d368 = true := by decide +kernel

private def d366 : MobiusCertTree := .branch d367 d368
private def d362 : MobiusCertTree := .branch d363 d366
private def d354 : MobiusCertTree := .branch d355 d362
private abbrev d372 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 56
private theorem p372 : mobiusTreeCheck cg 1200001 1 1076736 d372 = true := by decide +kernel

private abbrev d373 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 57
private theorem p373 : mobiusTreeCheck cg 1200001 1 1076800 d373 = true := by decide +kernel

private def d371 : MobiusCertTree := .branch d372 d373
private abbrev d375 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 58
private theorem p375 : mobiusTreeCheck cg 1200001 1 1076864 d375 = true := by decide +kernel

private abbrev d376 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 59
private theorem p376 : mobiusTreeCheck cg 1200001 1 1076928 d376 = true := by decide +kernel

private def d374 : MobiusCertTree := .branch d375 d376
private def d370 : MobiusCertTree := .branch d371 d374
private abbrev d379 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 60
private theorem p379 : mobiusTreeCheck cg 1200001 1 1076992 d379 = true := by decide +kernel

private abbrev d380 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 61
private theorem p380 : mobiusTreeCheck cg 1200001 1 1077056 d380 = true := by decide +kernel

private def d378 : MobiusCertTree := .branch d379 d380
private abbrev d382 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 62
private theorem p382 : mobiusTreeCheck cg 1200001 1 1077120 d382 = true := by decide +kernel

private abbrev d383 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 63
private theorem p383 : mobiusTreeCheck cg 1200001 1 1077184 d383 = true := by decide +kernel

private def d381 : MobiusCertTree := .branch d382 d383
private def d377 : MobiusCertTree := .branch d378 d381
private def d369 : MobiusCertTree := .branch d370 d377
private def d353 : MobiusCertTree := .branch d354 d369
private def d321 : MobiusCertTree := .branch d322 d353
private def d257 : MobiusCertTree := .branch d258 d321
private abbrev d390 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 64
private theorem p390 : mobiusTreeCheck cg 1200001 1 1077248 d390 = true := by decide +kernel

private abbrev d391 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 65
private theorem p391 : mobiusTreeCheck cg 1200001 1 1077312 d391 = true := by decide +kernel

private def d389 : MobiusCertTree := .branch d390 d391
private abbrev d393 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 66
private theorem p393 : mobiusTreeCheck cg 1200001 1 1077376 d393 = true := by decide +kernel

private abbrev d394 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 67
private theorem p394 : mobiusTreeCheck cg 1200001 1 1077440 d394 = true := by decide +kernel

private def d392 : MobiusCertTree := .branch d393 d394
private def d388 : MobiusCertTree := .branch d389 d392
private abbrev d397 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 68
private theorem p397 : mobiusTreeCheck cg 1200001 1 1077504 d397 = true := by decide +kernel

private abbrev d398 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 69
private theorem p398 : mobiusTreeCheck cg 1200001 1 1077568 d398 = true := by decide +kernel

private def d396 : MobiusCertTree := .branch d397 d398
private abbrev d400 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 70
private theorem p400 : mobiusTreeCheck cg 1200001 1 1077632 d400 = true := by decide +kernel

private abbrev d401 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 71
private theorem p401 : mobiusTreeCheck cg 1200001 1 1077696 d401 = true := by decide +kernel

private def d399 : MobiusCertTree := .branch d400 d401
private def d395 : MobiusCertTree := .branch d396 d399
private def d387 : MobiusCertTree := .branch d388 d395
private abbrev d405 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 72
private theorem p405 : mobiusTreeCheck cg 1200001 1 1077760 d405 = true := by decide +kernel

private abbrev d406 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 73
private theorem p406 : mobiusTreeCheck cg 1200001 1 1077824 d406 = true := by decide +kernel

private def d404 : MobiusCertTree := .branch d405 d406
private abbrev d408 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 74
private theorem p408 : mobiusTreeCheck cg 1200001 1 1077888 d408 = true := by decide +kernel

private abbrev d409 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 75
private theorem p409 : mobiusTreeCheck cg 1200001 1 1077952 d409 = true := by decide +kernel

private def d407 : MobiusCertTree := .branch d408 d409
private def d403 : MobiusCertTree := .branch d404 d407
private abbrev d412 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 76
private theorem p412 : mobiusTreeCheck cg 1200001 1 1078016 d412 = true := by decide +kernel

private abbrev d413 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 77
private theorem p413 : mobiusTreeCheck cg 1200001 1 1078080 d413 = true := by decide +kernel

private def d411 : MobiusCertTree := .branch d412 d413
private abbrev d415 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 78
private theorem p415 : mobiusTreeCheck cg 1200001 1 1078144 d415 = true := by decide +kernel

private abbrev d416 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 79
private theorem p416 : mobiusTreeCheck cg 1200001 1 1078208 d416 = true := by decide +kernel

private def d414 : MobiusCertTree := .branch d415 d416
private def d410 : MobiusCertTree := .branch d411 d414
private def d402 : MobiusCertTree := .branch d403 d410
private def d386 : MobiusCertTree := .branch d387 d402
private abbrev d421 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 80
private theorem p421 : mobiusTreeCheck cg 1200001 1 1078272 d421 = true := by decide +kernel

private abbrev d422 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 81
private theorem p422 : mobiusTreeCheck cg 1200001 1 1078336 d422 = true := by decide +kernel

private def d420 : MobiusCertTree := .branch d421 d422
private abbrev d424 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 82
private theorem p424 : mobiusTreeCheck cg 1200001 1 1078400 d424 = true := by decide +kernel

private abbrev d425 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 83
private theorem p425 : mobiusTreeCheck cg 1200001 1 1078464 d425 = true := by decide +kernel

private def d423 : MobiusCertTree := .branch d424 d425
private def d419 : MobiusCertTree := .branch d420 d423
private abbrev d428 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 84
private theorem p428 : mobiusTreeCheck cg 1200001 1 1078528 d428 = true := by decide +kernel

private abbrev d429 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 85
private theorem p429 : mobiusTreeCheck cg 1200001 1 1078592 d429 = true := by decide +kernel

private def d427 : MobiusCertTree := .branch d428 d429
private abbrev d431 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 86
private theorem p431 : mobiusTreeCheck cg 1200001 1 1078656 d431 = true := by decide +kernel

private abbrev d432 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 87
private theorem p432 : mobiusTreeCheck cg 1200001 1 1078720 d432 = true := by decide +kernel

private def d430 : MobiusCertTree := .branch d431 d432
private def d426 : MobiusCertTree := .branch d427 d430
private def d418 : MobiusCertTree := .branch d419 d426
private abbrev d436 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 88
private theorem p436 : mobiusTreeCheck cg 1200001 1 1078784 d436 = true := by decide +kernel

private abbrev d437 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 89
private theorem p437 : mobiusTreeCheck cg 1200001 1 1078848 d437 = true := by decide +kernel

private def d435 : MobiusCertTree := .branch d436 d437
private abbrev d439 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 90
private theorem p439 : mobiusTreeCheck cg 1200001 1 1078912 d439 = true := by decide +kernel

private abbrev d440 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 91
private theorem p440 : mobiusTreeCheck cg 1200001 1 1078976 d440 = true := by decide +kernel

private def d438 : MobiusCertTree := .branch d439 d440
private def d434 : MobiusCertTree := .branch d435 d438
private abbrev d443 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 92
private theorem p443 : mobiusTreeCheck cg 1200001 1 1079040 d443 = true := by decide +kernel

private abbrev d444 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 93
private theorem p444 : mobiusTreeCheck cg 1200001 1 1079104 d444 = true := by decide +kernel

private def d442 : MobiusCertTree := .branch d443 d444
private abbrev d446 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 94
private theorem p446 : mobiusTreeCheck cg 1200001 1 1079168 d446 = true := by decide +kernel

private abbrev d447 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 95
private theorem p447 : mobiusTreeCheck cg 1200001 1 1079232 d447 = true := by decide +kernel

private def d445 : MobiusCertTree := .branch d446 d447
private def d441 : MobiusCertTree := .branch d442 d445
private def d433 : MobiusCertTree := .branch d434 d441
private def d417 : MobiusCertTree := .branch d418 d433
private def d385 : MobiusCertTree := .branch d386 d417
private abbrev d453 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 96
private theorem p453 : mobiusTreeCheck cg 1200001 1 1079296 d453 = true := by decide +kernel

private abbrev d454 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 97
private theorem p454 : mobiusTreeCheck cg 1200001 1 1079360 d454 = true := by decide +kernel

private def d452 : MobiusCertTree := .branch d453 d454
private abbrev d456 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 98
private theorem p456 : mobiusTreeCheck cg 1200001 1 1079424 d456 = true := by decide +kernel

private abbrev d457 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 99
private theorem p457 : mobiusTreeCheck cg 1200001 1 1079488 d457 = true := by decide +kernel

private def d455 : MobiusCertTree := .branch d456 d457
private def d451 : MobiusCertTree := .branch d452 d455
private abbrev d460 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 100
private theorem p460 : mobiusTreeCheck cg 1200001 1 1079552 d460 = true := by decide +kernel

private abbrev d461 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 101
private theorem p461 : mobiusTreeCheck cg 1200001 1 1079616 d461 = true := by decide +kernel

private def d459 : MobiusCertTree := .branch d460 d461
private abbrev d463 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 102
private theorem p463 : mobiusTreeCheck cg 1200001 1 1079680 d463 = true := by decide +kernel

private abbrev d464 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 103
private theorem p464 : mobiusTreeCheck cg 1200001 1 1079744 d464 = true := by decide +kernel

private def d462 : MobiusCertTree := .branch d463 d464
private def d458 : MobiusCertTree := .branch d459 d462
private def d450 : MobiusCertTree := .branch d451 d458
private abbrev d468 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 104
private theorem p468 : mobiusTreeCheck cg 1200001 1 1079808 d468 = true := by decide +kernel

private abbrev d469 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 105
private theorem p469 : mobiusTreeCheck cg 1200001 1 1079872 d469 = true := by decide +kernel

private def d467 : MobiusCertTree := .branch d468 d469
private abbrev d471 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 106
private theorem p471 : mobiusTreeCheck cg 1200001 1 1079936 d471 = true := by decide +kernel

private abbrev d472 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 107
private theorem p472 : mobiusTreeCheck cg 1200001 1 1080000 d472 = true := by decide +kernel

private def d470 : MobiusCertTree := .branch d471 d472
private def d466 : MobiusCertTree := .branch d467 d470
private abbrev d475 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 108
private theorem p475 : mobiusTreeCheck cg 1200001 1 1080064 d475 = true := by decide +kernel

private abbrev d476 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 109
private theorem p476 : mobiusTreeCheck cg 1200001 1 1080128 d476 = true := by decide +kernel

private def d474 : MobiusCertTree := .branch d475 d476
private abbrev d478 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 110
private theorem p478 : mobiusTreeCheck cg 1200001 1 1080192 d478 = true := by decide +kernel

private abbrev d479 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 111
private theorem p479 : mobiusTreeCheck cg 1200001 1 1080256 d479 = true := by decide +kernel

private def d477 : MobiusCertTree := .branch d478 d479
private def d473 : MobiusCertTree := .branch d474 d477
private def d465 : MobiusCertTree := .branch d466 d473
private def d449 : MobiusCertTree := .branch d450 d465
private abbrev d484 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 112
private theorem p484 : mobiusTreeCheck cg 1200001 1 1080320 d484 = true := by decide +kernel

private abbrev d485 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 113
private theorem p485 : mobiusTreeCheck cg 1200001 1 1080384 d485 = true := by decide +kernel

private def d483 : MobiusCertTree := .branch d484 d485
private abbrev d487 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 114
private theorem p487 : mobiusTreeCheck cg 1200001 1 1080448 d487 = true := by decide +kernel

private abbrev d488 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 115
private theorem p488 : mobiusTreeCheck cg 1200001 1 1080512 d488 = true := by decide +kernel

private def d486 : MobiusCertTree := .branch d487 d488
private def d482 : MobiusCertTree := .branch d483 d486
private abbrev d491 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 116
private theorem p491 : mobiusTreeCheck cg 1200001 1 1080576 d491 = true := by decide +kernel

private abbrev d492 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 117
private theorem p492 : mobiusTreeCheck cg 1200001 1 1080640 d492 = true := by decide +kernel

private def d490 : MobiusCertTree := .branch d491 d492
private abbrev d494 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 118
private theorem p494 : mobiusTreeCheck cg 1200001 1 1080704 d494 = true := by decide +kernel

private abbrev d495 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 119
private theorem p495 : mobiusTreeCheck cg 1200001 1 1080768 d495 = true := by decide +kernel

private def d493 : MobiusCertTree := .branch d494 d495
private def d489 : MobiusCertTree := .branch d490 d493
private def d481 : MobiusCertTree := .branch d482 d489
private abbrev d499 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 120
private theorem p499 : mobiusTreeCheck cg 1200001 1 1080832 d499 = true := by decide +kernel

private abbrev d500 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 121
private theorem p500 : mobiusTreeCheck cg 1200001 1 1080896 d500 = true := by decide +kernel

private def d498 : MobiusCertTree := .branch d499 d500
private abbrev d502 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 122
private theorem p502 : mobiusTreeCheck cg 1200001 1 1080960 d502 = true := by decide +kernel

private abbrev d503 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 123
private theorem p503 : mobiusTreeCheck cg 1200001 1 1081024 d503 = true := by decide +kernel

private def d501 : MobiusCertTree := .branch d502 d503
private def d497 : MobiusCertTree := .branch d498 d501
private abbrev d506 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 124
private theorem p506 : mobiusTreeCheck cg 1200001 1 1081088 d506 = true := by decide +kernel

private abbrev d507 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 125
private theorem p507 : mobiusTreeCheck cg 1200001 1 1081152 d507 = true := by decide +kernel

private def d505 : MobiusCertTree := .branch d506 d507
private abbrev d509 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 126
private theorem p509 : mobiusTreeCheck cg 1200001 1 1081216 d509 = true := by decide +kernel

private abbrev d510 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock131 127
private theorem p510 : mobiusTreeCheck cg 1200001 1 1081280 d510 = true := by decide +kernel

private def d508 : MobiusCertTree := .branch d509 d510
private def d504 : MobiusCertTree := .branch d505 d508
private def d496 : MobiusCertTree := .branch d497 d504
private def d480 : MobiusCertTree := .branch d481 d496
private def d448 : MobiusCertTree := .branch d449 d480
private def d384 : MobiusCertTree := .branch d385 d448
private def d256 : MobiusCertTree := .branch d257 d384
private def d0 : MobiusCertTree := .branch d1 d256

private theorem combined : mobiusTreeCheck cg 1200001 9 1064960 d0 = true :=
  (mobiusTreeCheck_join cg 1200001 8 1064960 _ _ (mobiusTreeCheck_join cg 1200001 7 1064960 _ _ (mobiusTreeCheck_join cg 1200001 6 1064960 _ _ (mobiusTreeCheck_join cg 1200001 5 1064960 _ _ (mobiusTreeCheck_join cg 1200001 4 1064960 _ _ (mobiusTreeCheck_join cg 1200001 3 1064960 _ _ (mobiusTreeCheck_join cg 1200001 2 1064960 _ _ (mobiusTreeCheck_join cg 1200001 1 1064960 _ _ p8 p9) (mobiusTreeCheck_join cg 1200001 1 1065088 _ _ p11 p12)) (mobiusTreeCheck_join cg 1200001 2 1065216 _ _ (mobiusTreeCheck_join cg 1200001 1 1065216 _ _ p15 p16) (mobiusTreeCheck_join cg 1200001 1 1065344 _ _ p18 p19))) (mobiusTreeCheck_join cg 1200001 3 1065472 _ _ (mobiusTreeCheck_join cg 1200001 2 1065472 _ _ (mobiusTreeCheck_join cg 1200001 1 1065472 _ _ p23 p24) (mobiusTreeCheck_join cg 1200001 1 1065600 _ _ p26 p27)) (mobiusTreeCheck_join cg 1200001 2 1065728 _ _ (mobiusTreeCheck_join cg 1200001 1 1065728 _ _ p30 p31) (mobiusTreeCheck_join cg 1200001 1 1065856 _ _ p33 p34)))) (mobiusTreeCheck_join cg 1200001 4 1065984 _ _ (mobiusTreeCheck_join cg 1200001 3 1065984 _ _ (mobiusTreeCheck_join cg 1200001 2 1065984 _ _ (mobiusTreeCheck_join cg 1200001 1 1065984 _ _ p39 p40) (mobiusTreeCheck_join cg 1200001 1 1066112 _ _ p42 p43)) (mobiusTreeCheck_join cg 1200001 2 1066240 _ _ (mobiusTreeCheck_join cg 1200001 1 1066240 _ _ p46 p47) (mobiusTreeCheck_join cg 1200001 1 1066368 _ _ p49 p50))) (mobiusTreeCheck_join cg 1200001 3 1066496 _ _ (mobiusTreeCheck_join cg 1200001 2 1066496 _ _ (mobiusTreeCheck_join cg 1200001 1 1066496 _ _ p54 p55) (mobiusTreeCheck_join cg 1200001 1 1066624 _ _ p57 p58)) (mobiusTreeCheck_join cg 1200001 2 1066752 _ _ (mobiusTreeCheck_join cg 1200001 1 1066752 _ _ p61 p62) (mobiusTreeCheck_join cg 1200001 1 1066880 _ _ p64 p65))))) (mobiusTreeCheck_join cg 1200001 5 1067008 _ _ (mobiusTreeCheck_join cg 1200001 4 1067008 _ _ (mobiusTreeCheck_join cg 1200001 3 1067008 _ _ (mobiusTreeCheck_join cg 1200001 2 1067008 _ _ (mobiusTreeCheck_join cg 1200001 1 1067008 _ _ p71 p72) (mobiusTreeCheck_join cg 1200001 1 1067136 _ _ p74 p75)) (mobiusTreeCheck_join cg 1200001 2 1067264 _ _ (mobiusTreeCheck_join cg 1200001 1 1067264 _ _ p78 p79) (mobiusTreeCheck_join cg 1200001 1 1067392 _ _ p81 p82))) (mobiusTreeCheck_join cg 1200001 3 1067520 _ _ (mobiusTreeCheck_join cg 1200001 2 1067520 _ _ (mobiusTreeCheck_join cg 1200001 1 1067520 _ _ p86 p87) (mobiusTreeCheck_join cg 1200001 1 1067648 _ _ p89 p90)) (mobiusTreeCheck_join cg 1200001 2 1067776 _ _ (mobiusTreeCheck_join cg 1200001 1 1067776 _ _ p93 p94) (mobiusTreeCheck_join cg 1200001 1 1067904 _ _ p96 p97)))) (mobiusTreeCheck_join cg 1200001 4 1068032 _ _ (mobiusTreeCheck_join cg 1200001 3 1068032 _ _ (mobiusTreeCheck_join cg 1200001 2 1068032 _ _ (mobiusTreeCheck_join cg 1200001 1 1068032 _ _ p102 p103) (mobiusTreeCheck_join cg 1200001 1 1068160 _ _ p105 p106)) (mobiusTreeCheck_join cg 1200001 2 1068288 _ _ (mobiusTreeCheck_join cg 1200001 1 1068288 _ _ p109 p110) (mobiusTreeCheck_join cg 1200001 1 1068416 _ _ p112 p113))) (mobiusTreeCheck_join cg 1200001 3 1068544 _ _ (mobiusTreeCheck_join cg 1200001 2 1068544 _ _ (mobiusTreeCheck_join cg 1200001 1 1068544 _ _ p117 p118) (mobiusTreeCheck_join cg 1200001 1 1068672 _ _ p120 p121)) (mobiusTreeCheck_join cg 1200001 2 1068800 _ _ (mobiusTreeCheck_join cg 1200001 1 1068800 _ _ p124 p125) (mobiusTreeCheck_join cg 1200001 1 1068928 _ _ p127 p128)))))) (mobiusTreeCheck_join cg 1200001 6 1069056 _ _ (mobiusTreeCheck_join cg 1200001 5 1069056 _ _ (mobiusTreeCheck_join cg 1200001 4 1069056 _ _ (mobiusTreeCheck_join cg 1200001 3 1069056 _ _ (mobiusTreeCheck_join cg 1200001 2 1069056 _ _ (mobiusTreeCheck_join cg 1200001 1 1069056 _ _ p135 p136) (mobiusTreeCheck_join cg 1200001 1 1069184 _ _ p138 p139)) (mobiusTreeCheck_join cg 1200001 2 1069312 _ _ (mobiusTreeCheck_join cg 1200001 1 1069312 _ _ p142 p143) (mobiusTreeCheck_join cg 1200001 1 1069440 _ _ p145 p146))) (mobiusTreeCheck_join cg 1200001 3 1069568 _ _ (mobiusTreeCheck_join cg 1200001 2 1069568 _ _ (mobiusTreeCheck_join cg 1200001 1 1069568 _ _ p150 p151) (mobiusTreeCheck_join cg 1200001 1 1069696 _ _ p153 p154)) (mobiusTreeCheck_join cg 1200001 2 1069824 _ _ (mobiusTreeCheck_join cg 1200001 1 1069824 _ _ p157 p158) (mobiusTreeCheck_join cg 1200001 1 1069952 _ _ p160 p161)))) (mobiusTreeCheck_join cg 1200001 4 1070080 _ _ (mobiusTreeCheck_join cg 1200001 3 1070080 _ _ (mobiusTreeCheck_join cg 1200001 2 1070080 _ _ (mobiusTreeCheck_join cg 1200001 1 1070080 _ _ p166 p167) (mobiusTreeCheck_join cg 1200001 1 1070208 _ _ p169 p170)) (mobiusTreeCheck_join cg 1200001 2 1070336 _ _ (mobiusTreeCheck_join cg 1200001 1 1070336 _ _ p173 p174) (mobiusTreeCheck_join cg 1200001 1 1070464 _ _ p176 p177))) (mobiusTreeCheck_join cg 1200001 3 1070592 _ _ (mobiusTreeCheck_join cg 1200001 2 1070592 _ _ (mobiusTreeCheck_join cg 1200001 1 1070592 _ _ p181 p182) (mobiusTreeCheck_join cg 1200001 1 1070720 _ _ p184 p185)) (mobiusTreeCheck_join cg 1200001 2 1070848 _ _ (mobiusTreeCheck_join cg 1200001 1 1070848 _ _ p188 p189) (mobiusTreeCheck_join cg 1200001 1 1070976 _ _ p191 p192))))) (mobiusTreeCheck_join cg 1200001 5 1071104 _ _ (mobiusTreeCheck_join cg 1200001 4 1071104 _ _ (mobiusTreeCheck_join cg 1200001 3 1071104 _ _ (mobiusTreeCheck_join cg 1200001 2 1071104 _ _ (mobiusTreeCheck_join cg 1200001 1 1071104 _ _ p198 p199) (mobiusTreeCheck_join cg 1200001 1 1071232 _ _ p201 p202)) (mobiusTreeCheck_join cg 1200001 2 1071360 _ _ (mobiusTreeCheck_join cg 1200001 1 1071360 _ _ p205 p206) (mobiusTreeCheck_join cg 1200001 1 1071488 _ _ p208 p209))) (mobiusTreeCheck_join cg 1200001 3 1071616 _ _ (mobiusTreeCheck_join cg 1200001 2 1071616 _ _ (mobiusTreeCheck_join cg 1200001 1 1071616 _ _ p213 p214) (mobiusTreeCheck_join cg 1200001 1 1071744 _ _ p216 p217)) (mobiusTreeCheck_join cg 1200001 2 1071872 _ _ (mobiusTreeCheck_join cg 1200001 1 1071872 _ _ p220 p221) (mobiusTreeCheck_join cg 1200001 1 1072000 _ _ p223 p224)))) (mobiusTreeCheck_join cg 1200001 4 1072128 _ _ (mobiusTreeCheck_join cg 1200001 3 1072128 _ _ (mobiusTreeCheck_join cg 1200001 2 1072128 _ _ (mobiusTreeCheck_join cg 1200001 1 1072128 _ _ p229 p230) (mobiusTreeCheck_join cg 1200001 1 1072256 _ _ p232 p233)) (mobiusTreeCheck_join cg 1200001 2 1072384 _ _ (mobiusTreeCheck_join cg 1200001 1 1072384 _ _ p236 p237) (mobiusTreeCheck_join cg 1200001 1 1072512 _ _ p239 p240))) (mobiusTreeCheck_join cg 1200001 3 1072640 _ _ (mobiusTreeCheck_join cg 1200001 2 1072640 _ _ (mobiusTreeCheck_join cg 1200001 1 1072640 _ _ p244 p245) (mobiusTreeCheck_join cg 1200001 1 1072768 _ _ p247 p248)) (mobiusTreeCheck_join cg 1200001 2 1072896 _ _ (mobiusTreeCheck_join cg 1200001 1 1072896 _ _ p251 p252) (mobiusTreeCheck_join cg 1200001 1 1073024 _ _ p254 p255))))))) (mobiusTreeCheck_join cg 1200001 7 1073152 _ _ (mobiusTreeCheck_join cg 1200001 6 1073152 _ _ (mobiusTreeCheck_join cg 1200001 5 1073152 _ _ (mobiusTreeCheck_join cg 1200001 4 1073152 _ _ (mobiusTreeCheck_join cg 1200001 3 1073152 _ _ (mobiusTreeCheck_join cg 1200001 2 1073152 _ _ (mobiusTreeCheck_join cg 1200001 1 1073152 _ _ p263 p264) (mobiusTreeCheck_join cg 1200001 1 1073280 _ _ p266 p267)) (mobiusTreeCheck_join cg 1200001 2 1073408 _ _ (mobiusTreeCheck_join cg 1200001 1 1073408 _ _ p270 p271) (mobiusTreeCheck_join cg 1200001 1 1073536 _ _ p273 p274))) (mobiusTreeCheck_join cg 1200001 3 1073664 _ _ (mobiusTreeCheck_join cg 1200001 2 1073664 _ _ (mobiusTreeCheck_join cg 1200001 1 1073664 _ _ p278 p279) (mobiusTreeCheck_join cg 1200001 1 1073792 _ _ p281 p282)) (mobiusTreeCheck_join cg 1200001 2 1073920 _ _ (mobiusTreeCheck_join cg 1200001 1 1073920 _ _ p285 p286) (mobiusTreeCheck_join cg 1200001 1 1074048 _ _ p288 p289)))) (mobiusTreeCheck_join cg 1200001 4 1074176 _ _ (mobiusTreeCheck_join cg 1200001 3 1074176 _ _ (mobiusTreeCheck_join cg 1200001 2 1074176 _ _ (mobiusTreeCheck_join cg 1200001 1 1074176 _ _ p294 p295) (mobiusTreeCheck_join cg 1200001 1 1074304 _ _ p297 p298)) (mobiusTreeCheck_join cg 1200001 2 1074432 _ _ (mobiusTreeCheck_join cg 1200001 1 1074432 _ _ p301 p302) (mobiusTreeCheck_join cg 1200001 1 1074560 _ _ p304 p305))) (mobiusTreeCheck_join cg 1200001 3 1074688 _ _ (mobiusTreeCheck_join cg 1200001 2 1074688 _ _ (mobiusTreeCheck_join cg 1200001 1 1074688 _ _ p309 p310) (mobiusTreeCheck_join cg 1200001 1 1074816 _ _ p312 p313)) (mobiusTreeCheck_join cg 1200001 2 1074944 _ _ (mobiusTreeCheck_join cg 1200001 1 1074944 _ _ p316 p317) (mobiusTreeCheck_join cg 1200001 1 1075072 _ _ p319 p320))))) (mobiusTreeCheck_join cg 1200001 5 1075200 _ _ (mobiusTreeCheck_join cg 1200001 4 1075200 _ _ (mobiusTreeCheck_join cg 1200001 3 1075200 _ _ (mobiusTreeCheck_join cg 1200001 2 1075200 _ _ (mobiusTreeCheck_join cg 1200001 1 1075200 _ _ p326 p327) (mobiusTreeCheck_join cg 1200001 1 1075328 _ _ p329 p330)) (mobiusTreeCheck_join cg 1200001 2 1075456 _ _ (mobiusTreeCheck_join cg 1200001 1 1075456 _ _ p333 p334) (mobiusTreeCheck_join cg 1200001 1 1075584 _ _ p336 p337))) (mobiusTreeCheck_join cg 1200001 3 1075712 _ _ (mobiusTreeCheck_join cg 1200001 2 1075712 _ _ (mobiusTreeCheck_join cg 1200001 1 1075712 _ _ p341 p342) (mobiusTreeCheck_join cg 1200001 1 1075840 _ _ p344 p345)) (mobiusTreeCheck_join cg 1200001 2 1075968 _ _ (mobiusTreeCheck_join cg 1200001 1 1075968 _ _ p348 p349) (mobiusTreeCheck_join cg 1200001 1 1076096 _ _ p351 p352)))) (mobiusTreeCheck_join cg 1200001 4 1076224 _ _ (mobiusTreeCheck_join cg 1200001 3 1076224 _ _ (mobiusTreeCheck_join cg 1200001 2 1076224 _ _ (mobiusTreeCheck_join cg 1200001 1 1076224 _ _ p357 p358) (mobiusTreeCheck_join cg 1200001 1 1076352 _ _ p360 p361)) (mobiusTreeCheck_join cg 1200001 2 1076480 _ _ (mobiusTreeCheck_join cg 1200001 1 1076480 _ _ p364 p365) (mobiusTreeCheck_join cg 1200001 1 1076608 _ _ p367 p368))) (mobiusTreeCheck_join cg 1200001 3 1076736 _ _ (mobiusTreeCheck_join cg 1200001 2 1076736 _ _ (mobiusTreeCheck_join cg 1200001 1 1076736 _ _ p372 p373) (mobiusTreeCheck_join cg 1200001 1 1076864 _ _ p375 p376)) (mobiusTreeCheck_join cg 1200001 2 1076992 _ _ (mobiusTreeCheck_join cg 1200001 1 1076992 _ _ p379 p380) (mobiusTreeCheck_join cg 1200001 1 1077120 _ _ p382 p383)))))) (mobiusTreeCheck_join cg 1200001 6 1077248 _ _ (mobiusTreeCheck_join cg 1200001 5 1077248 _ _ (mobiusTreeCheck_join cg 1200001 4 1077248 _ _ (mobiusTreeCheck_join cg 1200001 3 1077248 _ _ (mobiusTreeCheck_join cg 1200001 2 1077248 _ _ (mobiusTreeCheck_join cg 1200001 1 1077248 _ _ p390 p391) (mobiusTreeCheck_join cg 1200001 1 1077376 _ _ p393 p394)) (mobiusTreeCheck_join cg 1200001 2 1077504 _ _ (mobiusTreeCheck_join cg 1200001 1 1077504 _ _ p397 p398) (mobiusTreeCheck_join cg 1200001 1 1077632 _ _ p400 p401))) (mobiusTreeCheck_join cg 1200001 3 1077760 _ _ (mobiusTreeCheck_join cg 1200001 2 1077760 _ _ (mobiusTreeCheck_join cg 1200001 1 1077760 _ _ p405 p406) (mobiusTreeCheck_join cg 1200001 1 1077888 _ _ p408 p409)) (mobiusTreeCheck_join cg 1200001 2 1078016 _ _ (mobiusTreeCheck_join cg 1200001 1 1078016 _ _ p412 p413) (mobiusTreeCheck_join cg 1200001 1 1078144 _ _ p415 p416)))) (mobiusTreeCheck_join cg 1200001 4 1078272 _ _ (mobiusTreeCheck_join cg 1200001 3 1078272 _ _ (mobiusTreeCheck_join cg 1200001 2 1078272 _ _ (mobiusTreeCheck_join cg 1200001 1 1078272 _ _ p421 p422) (mobiusTreeCheck_join cg 1200001 1 1078400 _ _ p424 p425)) (mobiusTreeCheck_join cg 1200001 2 1078528 _ _ (mobiusTreeCheck_join cg 1200001 1 1078528 _ _ p428 p429) (mobiusTreeCheck_join cg 1200001 1 1078656 _ _ p431 p432))) (mobiusTreeCheck_join cg 1200001 3 1078784 _ _ (mobiusTreeCheck_join cg 1200001 2 1078784 _ _ (mobiusTreeCheck_join cg 1200001 1 1078784 _ _ p436 p437) (mobiusTreeCheck_join cg 1200001 1 1078912 _ _ p439 p440)) (mobiusTreeCheck_join cg 1200001 2 1079040 _ _ (mobiusTreeCheck_join cg 1200001 1 1079040 _ _ p443 p444) (mobiusTreeCheck_join cg 1200001 1 1079168 _ _ p446 p447))))) (mobiusTreeCheck_join cg 1200001 5 1079296 _ _ (mobiusTreeCheck_join cg 1200001 4 1079296 _ _ (mobiusTreeCheck_join cg 1200001 3 1079296 _ _ (mobiusTreeCheck_join cg 1200001 2 1079296 _ _ (mobiusTreeCheck_join cg 1200001 1 1079296 _ _ p453 p454) (mobiusTreeCheck_join cg 1200001 1 1079424 _ _ p456 p457)) (mobiusTreeCheck_join cg 1200001 2 1079552 _ _ (mobiusTreeCheck_join cg 1200001 1 1079552 _ _ p460 p461) (mobiusTreeCheck_join cg 1200001 1 1079680 _ _ p463 p464))) (mobiusTreeCheck_join cg 1200001 3 1079808 _ _ (mobiusTreeCheck_join cg 1200001 2 1079808 _ _ (mobiusTreeCheck_join cg 1200001 1 1079808 _ _ p468 p469) (mobiusTreeCheck_join cg 1200001 1 1079936 _ _ p471 p472)) (mobiusTreeCheck_join cg 1200001 2 1080064 _ _ (mobiusTreeCheck_join cg 1200001 1 1080064 _ _ p475 p476) (mobiusTreeCheck_join cg 1200001 1 1080192 _ _ p478 p479)))) (mobiusTreeCheck_join cg 1200001 4 1080320 _ _ (mobiusTreeCheck_join cg 1200001 3 1080320 _ _ (mobiusTreeCheck_join cg 1200001 2 1080320 _ _ (mobiusTreeCheck_join cg 1200001 1 1080320 _ _ p484 p485) (mobiusTreeCheck_join cg 1200001 1 1080448 _ _ p487 p488)) (mobiusTreeCheck_join cg 1200001 2 1080576 _ _ (mobiusTreeCheck_join cg 1200001 1 1080576 _ _ p491 p492) (mobiusTreeCheck_join cg 1200001 1 1080704 _ _ p494 p495))) (mobiusTreeCheck_join cg 1200001 3 1080832 _ _ (mobiusTreeCheck_join cg 1200001 2 1080832 _ _ (mobiusTreeCheck_join cg 1200001 1 1080832 _ _ p499 p500) (mobiusTreeCheck_join cg 1200001 1 1080960 _ _ p502 p503)) (mobiusTreeCheck_join cg 1200001 2 1081088 _ _ (mobiusTreeCheck_join cg 1200001 1 1081088 _ _ p506 p507) (mobiusTreeCheck_join cg 1200001 1 1081216 _ _ p509 p510))))))))

end Helfgott

open Helfgott
theorem solution : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 1064960 (MobiusCertTree.branch mobiusTableBlock130 mobiusTableBlock131) = true := Helfgott.combined

#print axioms solution
