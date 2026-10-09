-- Prove2me | solution 1 for Helfgott.mobiusValuePair044_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:35:32.24754+00:00
-- url     : https://prove2.me/submissions/7aa983e9-6726-4526-85d5-09e459e9112b

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

private abbrev d8 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 0
private theorem p8 : mobiusTreeCheck cg 1200001 1 720896 d8 = true := by decide +kernel

private abbrev d9 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 1
private theorem p9 : mobiusTreeCheck cg 1200001 1 720960 d9 = true := by decide +kernel

private def d7 : MobiusCertTree := .branch d8 d9
private abbrev d11 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 2
private theorem p11 : mobiusTreeCheck cg 1200001 1 721024 d11 = true := by decide +kernel

private abbrev d12 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 3
private theorem p12 : mobiusTreeCheck cg 1200001 1 721088 d12 = true := by decide +kernel

private def d10 : MobiusCertTree := .branch d11 d12
private def d6 : MobiusCertTree := .branch d7 d10
private abbrev d15 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 4
private theorem p15 : mobiusTreeCheck cg 1200001 1 721152 d15 = true := by decide +kernel

private abbrev d16 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 5
private theorem p16 : mobiusTreeCheck cg 1200001 1 721216 d16 = true := by decide +kernel

private def d14 : MobiusCertTree := .branch d15 d16
private abbrev d18 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 6
private theorem p18 : mobiusTreeCheck cg 1200001 1 721280 d18 = true := by decide +kernel

private abbrev d19 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 7
private theorem p19 : mobiusTreeCheck cg 1200001 1 721344 d19 = true := by decide +kernel

private def d17 : MobiusCertTree := .branch d18 d19
private def d13 : MobiusCertTree := .branch d14 d17
private def d5 : MobiusCertTree := .branch d6 d13
private abbrev d23 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 8
private theorem p23 : mobiusTreeCheck cg 1200001 1 721408 d23 = true := by decide +kernel

private abbrev d24 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 9
private theorem p24 : mobiusTreeCheck cg 1200001 1 721472 d24 = true := by decide +kernel

private def d22 : MobiusCertTree := .branch d23 d24
private abbrev d26 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 10
private theorem p26 : mobiusTreeCheck cg 1200001 1 721536 d26 = true := by decide +kernel

private abbrev d27 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 11
private theorem p27 : mobiusTreeCheck cg 1200001 1 721600 d27 = true := by decide +kernel

private def d25 : MobiusCertTree := .branch d26 d27
private def d21 : MobiusCertTree := .branch d22 d25
private abbrev d30 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 12
private theorem p30 : mobiusTreeCheck cg 1200001 1 721664 d30 = true := by decide +kernel

private abbrev d31 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 13
private theorem p31 : mobiusTreeCheck cg 1200001 1 721728 d31 = true := by decide +kernel

private def d29 : MobiusCertTree := .branch d30 d31
private abbrev d33 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 14
private theorem p33 : mobiusTreeCheck cg 1200001 1 721792 d33 = true := by decide +kernel

private abbrev d34 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 15
private theorem p34 : mobiusTreeCheck cg 1200001 1 721856 d34 = true := by decide +kernel

private def d32 : MobiusCertTree := .branch d33 d34
private def d28 : MobiusCertTree := .branch d29 d32
private def d20 : MobiusCertTree := .branch d21 d28
private def d4 : MobiusCertTree := .branch d5 d20
private abbrev d39 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 16
private theorem p39 : mobiusTreeCheck cg 1200001 1 721920 d39 = true := by decide +kernel

private abbrev d40 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 17
private theorem p40 : mobiusTreeCheck cg 1200001 1 721984 d40 = true := by decide +kernel

private def d38 : MobiusCertTree := .branch d39 d40
private abbrev d42 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 18
private theorem p42 : mobiusTreeCheck cg 1200001 1 722048 d42 = true := by decide +kernel

private abbrev d43 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 19
private theorem p43 : mobiusTreeCheck cg 1200001 1 722112 d43 = true := by decide +kernel

private def d41 : MobiusCertTree := .branch d42 d43
private def d37 : MobiusCertTree := .branch d38 d41
private abbrev d46 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 20
private theorem p46 : mobiusTreeCheck cg 1200001 1 722176 d46 = true := by decide +kernel

private abbrev d47 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 21
private theorem p47 : mobiusTreeCheck cg 1200001 1 722240 d47 = true := by decide +kernel

private def d45 : MobiusCertTree := .branch d46 d47
private abbrev d49 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 22
private theorem p49 : mobiusTreeCheck cg 1200001 1 722304 d49 = true := by decide +kernel

private abbrev d50 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 23
private theorem p50 : mobiusTreeCheck cg 1200001 1 722368 d50 = true := by decide +kernel

private def d48 : MobiusCertTree := .branch d49 d50
private def d44 : MobiusCertTree := .branch d45 d48
private def d36 : MobiusCertTree := .branch d37 d44
private abbrev d54 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 24
private theorem p54 : mobiusTreeCheck cg 1200001 1 722432 d54 = true := by decide +kernel

private abbrev d55 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 25
private theorem p55 : mobiusTreeCheck cg 1200001 1 722496 d55 = true := by decide +kernel

private def d53 : MobiusCertTree := .branch d54 d55
private abbrev d57 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 26
private theorem p57 : mobiusTreeCheck cg 1200001 1 722560 d57 = true := by decide +kernel

private abbrev d58 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 27
private theorem p58 : mobiusTreeCheck cg 1200001 1 722624 d58 = true := by decide +kernel

private def d56 : MobiusCertTree := .branch d57 d58
private def d52 : MobiusCertTree := .branch d53 d56
private abbrev d61 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 28
private theorem p61 : mobiusTreeCheck cg 1200001 1 722688 d61 = true := by decide +kernel

private abbrev d62 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 29
private theorem p62 : mobiusTreeCheck cg 1200001 1 722752 d62 = true := by decide +kernel

private def d60 : MobiusCertTree := .branch d61 d62
private abbrev d64 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 30
private theorem p64 : mobiusTreeCheck cg 1200001 1 722816 d64 = true := by decide +kernel

private abbrev d65 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 31
private theorem p65 : mobiusTreeCheck cg 1200001 1 722880 d65 = true := by decide +kernel

private def d63 : MobiusCertTree := .branch d64 d65
private def d59 : MobiusCertTree := .branch d60 d63
private def d51 : MobiusCertTree := .branch d52 d59
private def d35 : MobiusCertTree := .branch d36 d51
private def d3 : MobiusCertTree := .branch d4 d35
private abbrev d71 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 32
private theorem p71 : mobiusTreeCheck cg 1200001 1 722944 d71 = true := by decide +kernel

private abbrev d72 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 33
private theorem p72 : mobiusTreeCheck cg 1200001 1 723008 d72 = true := by decide +kernel

private def d70 : MobiusCertTree := .branch d71 d72
private abbrev d74 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 34
private theorem p74 : mobiusTreeCheck cg 1200001 1 723072 d74 = true := by decide +kernel

private abbrev d75 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 35
private theorem p75 : mobiusTreeCheck cg 1200001 1 723136 d75 = true := by decide +kernel

private def d73 : MobiusCertTree := .branch d74 d75
private def d69 : MobiusCertTree := .branch d70 d73
private abbrev d78 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 36
private theorem p78 : mobiusTreeCheck cg 1200001 1 723200 d78 = true := by decide +kernel

private abbrev d79 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 37
private theorem p79 : mobiusTreeCheck cg 1200001 1 723264 d79 = true := by decide +kernel

private def d77 : MobiusCertTree := .branch d78 d79
private abbrev d81 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 38
private theorem p81 : mobiusTreeCheck cg 1200001 1 723328 d81 = true := by decide +kernel

private abbrev d82 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 39
private theorem p82 : mobiusTreeCheck cg 1200001 1 723392 d82 = true := by decide +kernel

private def d80 : MobiusCertTree := .branch d81 d82
private def d76 : MobiusCertTree := .branch d77 d80
private def d68 : MobiusCertTree := .branch d69 d76
private abbrev d86 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 40
private theorem p86 : mobiusTreeCheck cg 1200001 1 723456 d86 = true := by decide +kernel

private abbrev d87 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 41
private theorem p87 : mobiusTreeCheck cg 1200001 1 723520 d87 = true := by decide +kernel

private def d85 : MobiusCertTree := .branch d86 d87
private abbrev d89 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 42
private theorem p89 : mobiusTreeCheck cg 1200001 1 723584 d89 = true := by decide +kernel

private abbrev d90 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 43
private theorem p90 : mobiusTreeCheck cg 1200001 1 723648 d90 = true := by decide +kernel

private def d88 : MobiusCertTree := .branch d89 d90
private def d84 : MobiusCertTree := .branch d85 d88
private abbrev d93 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 44
private theorem p93 : mobiusTreeCheck cg 1200001 1 723712 d93 = true := by decide +kernel

private abbrev d94 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 45
private theorem p94 : mobiusTreeCheck cg 1200001 1 723776 d94 = true := by decide +kernel

private def d92 : MobiusCertTree := .branch d93 d94
private abbrev d96 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 46
private theorem p96 : mobiusTreeCheck cg 1200001 1 723840 d96 = true := by decide +kernel

private abbrev d97 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 47
private theorem p97 : mobiusTreeCheck cg 1200001 1 723904 d97 = true := by decide +kernel

private def d95 : MobiusCertTree := .branch d96 d97
private def d91 : MobiusCertTree := .branch d92 d95
private def d83 : MobiusCertTree := .branch d84 d91
private def d67 : MobiusCertTree := .branch d68 d83
private abbrev d102 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 48
private theorem p102 : mobiusTreeCheck cg 1200001 1 723968 d102 = true := by decide +kernel

private abbrev d103 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 49
private theorem p103 : mobiusTreeCheck cg 1200001 1 724032 d103 = true := by decide +kernel

private def d101 : MobiusCertTree := .branch d102 d103
private abbrev d105 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 50
private theorem p105 : mobiusTreeCheck cg 1200001 1 724096 d105 = true := by decide +kernel

private abbrev d106 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 51
private theorem p106 : mobiusTreeCheck cg 1200001 1 724160 d106 = true := by decide +kernel

private def d104 : MobiusCertTree := .branch d105 d106
private def d100 : MobiusCertTree := .branch d101 d104
private abbrev d109 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 52
private theorem p109 : mobiusTreeCheck cg 1200001 1 724224 d109 = true := by decide +kernel

private abbrev d110 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 53
private theorem p110 : mobiusTreeCheck cg 1200001 1 724288 d110 = true := by decide +kernel

private def d108 : MobiusCertTree := .branch d109 d110
private abbrev d112 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 54
private theorem p112 : mobiusTreeCheck cg 1200001 1 724352 d112 = true := by decide +kernel

private abbrev d113 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 55
private theorem p113 : mobiusTreeCheck cg 1200001 1 724416 d113 = true := by decide +kernel

private def d111 : MobiusCertTree := .branch d112 d113
private def d107 : MobiusCertTree := .branch d108 d111
private def d99 : MobiusCertTree := .branch d100 d107
private abbrev d117 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 56
private theorem p117 : mobiusTreeCheck cg 1200001 1 724480 d117 = true := by decide +kernel

private abbrev d118 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 57
private theorem p118 : mobiusTreeCheck cg 1200001 1 724544 d118 = true := by decide +kernel

private def d116 : MobiusCertTree := .branch d117 d118
private abbrev d120 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 58
private theorem p120 : mobiusTreeCheck cg 1200001 1 724608 d120 = true := by decide +kernel

private abbrev d121 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 59
private theorem p121 : mobiusTreeCheck cg 1200001 1 724672 d121 = true := by decide +kernel

private def d119 : MobiusCertTree := .branch d120 d121
private def d115 : MobiusCertTree := .branch d116 d119
private abbrev d124 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 60
private theorem p124 : mobiusTreeCheck cg 1200001 1 724736 d124 = true := by decide +kernel

private abbrev d125 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 61
private theorem p125 : mobiusTreeCheck cg 1200001 1 724800 d125 = true := by decide +kernel

private def d123 : MobiusCertTree := .branch d124 d125
private abbrev d127 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 62
private theorem p127 : mobiusTreeCheck cg 1200001 1 724864 d127 = true := by decide +kernel

private abbrev d128 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 63
private theorem p128 : mobiusTreeCheck cg 1200001 1 724928 d128 = true := by decide +kernel

private def d126 : MobiusCertTree := .branch d127 d128
private def d122 : MobiusCertTree := .branch d123 d126
private def d114 : MobiusCertTree := .branch d115 d122
private def d98 : MobiusCertTree := .branch d99 d114
private def d66 : MobiusCertTree := .branch d67 d98
private def d2 : MobiusCertTree := .branch d3 d66
private abbrev d135 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 64
private theorem p135 : mobiusTreeCheck cg 1200001 1 724992 d135 = true := by decide +kernel

private abbrev d136 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 65
private theorem p136 : mobiusTreeCheck cg 1200001 1 725056 d136 = true := by decide +kernel

private def d134 : MobiusCertTree := .branch d135 d136
private abbrev d138 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 66
private theorem p138 : mobiusTreeCheck cg 1200001 1 725120 d138 = true := by decide +kernel

private abbrev d139 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 67
private theorem p139 : mobiusTreeCheck cg 1200001 1 725184 d139 = true := by decide +kernel

private def d137 : MobiusCertTree := .branch d138 d139
private def d133 : MobiusCertTree := .branch d134 d137
private abbrev d142 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 68
private theorem p142 : mobiusTreeCheck cg 1200001 1 725248 d142 = true := by decide +kernel

private abbrev d143 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 69
private theorem p143 : mobiusTreeCheck cg 1200001 1 725312 d143 = true := by decide +kernel

private def d141 : MobiusCertTree := .branch d142 d143
private abbrev d145 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 70
private theorem p145 : mobiusTreeCheck cg 1200001 1 725376 d145 = true := by decide +kernel

private abbrev d146 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 71
private theorem p146 : mobiusTreeCheck cg 1200001 1 725440 d146 = true := by decide +kernel

private def d144 : MobiusCertTree := .branch d145 d146
private def d140 : MobiusCertTree := .branch d141 d144
private def d132 : MobiusCertTree := .branch d133 d140
private abbrev d150 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 72
private theorem p150 : mobiusTreeCheck cg 1200001 1 725504 d150 = true := by decide +kernel

private abbrev d151 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 73
private theorem p151 : mobiusTreeCheck cg 1200001 1 725568 d151 = true := by decide +kernel

private def d149 : MobiusCertTree := .branch d150 d151
private abbrev d153 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 74
private theorem p153 : mobiusTreeCheck cg 1200001 1 725632 d153 = true := by decide +kernel

private abbrev d154 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 75
private theorem p154 : mobiusTreeCheck cg 1200001 1 725696 d154 = true := by decide +kernel

private def d152 : MobiusCertTree := .branch d153 d154
private def d148 : MobiusCertTree := .branch d149 d152
private abbrev d157 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 76
private theorem p157 : mobiusTreeCheck cg 1200001 1 725760 d157 = true := by decide +kernel

private abbrev d158 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 77
private theorem p158 : mobiusTreeCheck cg 1200001 1 725824 d158 = true := by decide +kernel

private def d156 : MobiusCertTree := .branch d157 d158
private abbrev d160 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 78
private theorem p160 : mobiusTreeCheck cg 1200001 1 725888 d160 = true := by decide +kernel

private abbrev d161 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 79
private theorem p161 : mobiusTreeCheck cg 1200001 1 725952 d161 = true := by decide +kernel

private def d159 : MobiusCertTree := .branch d160 d161
private def d155 : MobiusCertTree := .branch d156 d159
private def d147 : MobiusCertTree := .branch d148 d155
private def d131 : MobiusCertTree := .branch d132 d147
private abbrev d166 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 80
private theorem p166 : mobiusTreeCheck cg 1200001 1 726016 d166 = true := by decide +kernel

private abbrev d167 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 81
private theorem p167 : mobiusTreeCheck cg 1200001 1 726080 d167 = true := by decide +kernel

private def d165 : MobiusCertTree := .branch d166 d167
private abbrev d169 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 82
private theorem p169 : mobiusTreeCheck cg 1200001 1 726144 d169 = true := by decide +kernel

private abbrev d170 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 83
private theorem p170 : mobiusTreeCheck cg 1200001 1 726208 d170 = true := by decide +kernel

private def d168 : MobiusCertTree := .branch d169 d170
private def d164 : MobiusCertTree := .branch d165 d168
private abbrev d173 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 84
private theorem p173 : mobiusTreeCheck cg 1200001 1 726272 d173 = true := by decide +kernel

private abbrev d174 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 85
private theorem p174 : mobiusTreeCheck cg 1200001 1 726336 d174 = true := by decide +kernel

private def d172 : MobiusCertTree := .branch d173 d174
private abbrev d176 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 86
private theorem p176 : mobiusTreeCheck cg 1200001 1 726400 d176 = true := by decide +kernel

private abbrev d177 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 87
private theorem p177 : mobiusTreeCheck cg 1200001 1 726464 d177 = true := by decide +kernel

private def d175 : MobiusCertTree := .branch d176 d177
private def d171 : MobiusCertTree := .branch d172 d175
private def d163 : MobiusCertTree := .branch d164 d171
private abbrev d181 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 88
private theorem p181 : mobiusTreeCheck cg 1200001 1 726528 d181 = true := by decide +kernel

private abbrev d182 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 89
private theorem p182 : mobiusTreeCheck cg 1200001 1 726592 d182 = true := by decide +kernel

private def d180 : MobiusCertTree := .branch d181 d182
private abbrev d184 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 90
private theorem p184 : mobiusTreeCheck cg 1200001 1 726656 d184 = true := by decide +kernel

private abbrev d185 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 91
private theorem p185 : mobiusTreeCheck cg 1200001 1 726720 d185 = true := by decide +kernel

private def d183 : MobiusCertTree := .branch d184 d185
private def d179 : MobiusCertTree := .branch d180 d183
private abbrev d188 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 92
private theorem p188 : mobiusTreeCheck cg 1200001 1 726784 d188 = true := by decide +kernel

private abbrev d189 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 93
private theorem p189 : mobiusTreeCheck cg 1200001 1 726848 d189 = true := by decide +kernel

private def d187 : MobiusCertTree := .branch d188 d189
private abbrev d191 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 94
private theorem p191 : mobiusTreeCheck cg 1200001 1 726912 d191 = true := by decide +kernel

private abbrev d192 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 95
private theorem p192 : mobiusTreeCheck cg 1200001 1 726976 d192 = true := by decide +kernel

private def d190 : MobiusCertTree := .branch d191 d192
private def d186 : MobiusCertTree := .branch d187 d190
private def d178 : MobiusCertTree := .branch d179 d186
private def d162 : MobiusCertTree := .branch d163 d178
private def d130 : MobiusCertTree := .branch d131 d162
private abbrev d198 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 96
private theorem p198 : mobiusTreeCheck cg 1200001 1 727040 d198 = true := by decide +kernel

private abbrev d199 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 97
private theorem p199 : mobiusTreeCheck cg 1200001 1 727104 d199 = true := by decide +kernel

private def d197 : MobiusCertTree := .branch d198 d199
private abbrev d201 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 98
private theorem p201 : mobiusTreeCheck cg 1200001 1 727168 d201 = true := by decide +kernel

private abbrev d202 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 99
private theorem p202 : mobiusTreeCheck cg 1200001 1 727232 d202 = true := by decide +kernel

private def d200 : MobiusCertTree := .branch d201 d202
private def d196 : MobiusCertTree := .branch d197 d200
private abbrev d205 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 100
private theorem p205 : mobiusTreeCheck cg 1200001 1 727296 d205 = true := by decide +kernel

private abbrev d206 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 101
private theorem p206 : mobiusTreeCheck cg 1200001 1 727360 d206 = true := by decide +kernel

private def d204 : MobiusCertTree := .branch d205 d206
private abbrev d208 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 102
private theorem p208 : mobiusTreeCheck cg 1200001 1 727424 d208 = true := by decide +kernel

private abbrev d209 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 103
private theorem p209 : mobiusTreeCheck cg 1200001 1 727488 d209 = true := by decide +kernel

private def d207 : MobiusCertTree := .branch d208 d209
private def d203 : MobiusCertTree := .branch d204 d207
private def d195 : MobiusCertTree := .branch d196 d203
private abbrev d213 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 104
private theorem p213 : mobiusTreeCheck cg 1200001 1 727552 d213 = true := by decide +kernel

private abbrev d214 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 105
private theorem p214 : mobiusTreeCheck cg 1200001 1 727616 d214 = true := by decide +kernel

private def d212 : MobiusCertTree := .branch d213 d214
private abbrev d216 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 106
private theorem p216 : mobiusTreeCheck cg 1200001 1 727680 d216 = true := by decide +kernel

private abbrev d217 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 107
private theorem p217 : mobiusTreeCheck cg 1200001 1 727744 d217 = true := by decide +kernel

private def d215 : MobiusCertTree := .branch d216 d217
private def d211 : MobiusCertTree := .branch d212 d215
private abbrev d220 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 108
private theorem p220 : mobiusTreeCheck cg 1200001 1 727808 d220 = true := by decide +kernel

private abbrev d221 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 109
private theorem p221 : mobiusTreeCheck cg 1200001 1 727872 d221 = true := by decide +kernel

private def d219 : MobiusCertTree := .branch d220 d221
private abbrev d223 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 110
private theorem p223 : mobiusTreeCheck cg 1200001 1 727936 d223 = true := by decide +kernel

private abbrev d224 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 111
private theorem p224 : mobiusTreeCheck cg 1200001 1 728000 d224 = true := by decide +kernel

private def d222 : MobiusCertTree := .branch d223 d224
private def d218 : MobiusCertTree := .branch d219 d222
private def d210 : MobiusCertTree := .branch d211 d218
private def d194 : MobiusCertTree := .branch d195 d210
private abbrev d229 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 112
private theorem p229 : mobiusTreeCheck cg 1200001 1 728064 d229 = true := by decide +kernel

private abbrev d230 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 113
private theorem p230 : mobiusTreeCheck cg 1200001 1 728128 d230 = true := by decide +kernel

private def d228 : MobiusCertTree := .branch d229 d230
private abbrev d232 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 114
private theorem p232 : mobiusTreeCheck cg 1200001 1 728192 d232 = true := by decide +kernel

private abbrev d233 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 115
private theorem p233 : mobiusTreeCheck cg 1200001 1 728256 d233 = true := by decide +kernel

private def d231 : MobiusCertTree := .branch d232 d233
private def d227 : MobiusCertTree := .branch d228 d231
private abbrev d236 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 116
private theorem p236 : mobiusTreeCheck cg 1200001 1 728320 d236 = true := by decide +kernel

private abbrev d237 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 117
private theorem p237 : mobiusTreeCheck cg 1200001 1 728384 d237 = true := by decide +kernel

private def d235 : MobiusCertTree := .branch d236 d237
private abbrev d239 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 118
private theorem p239 : mobiusTreeCheck cg 1200001 1 728448 d239 = true := by decide +kernel

private abbrev d240 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 119
private theorem p240 : mobiusTreeCheck cg 1200001 1 728512 d240 = true := by decide +kernel

private def d238 : MobiusCertTree := .branch d239 d240
private def d234 : MobiusCertTree := .branch d235 d238
private def d226 : MobiusCertTree := .branch d227 d234
private abbrev d244 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 120
private theorem p244 : mobiusTreeCheck cg 1200001 1 728576 d244 = true := by decide +kernel

private abbrev d245 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 121
private theorem p245 : mobiusTreeCheck cg 1200001 1 728640 d245 = true := by decide +kernel

private def d243 : MobiusCertTree := .branch d244 d245
private abbrev d247 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 122
private theorem p247 : mobiusTreeCheck cg 1200001 1 728704 d247 = true := by decide +kernel

private abbrev d248 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 123
private theorem p248 : mobiusTreeCheck cg 1200001 1 728768 d248 = true := by decide +kernel

private def d246 : MobiusCertTree := .branch d247 d248
private def d242 : MobiusCertTree := .branch d243 d246
private abbrev d251 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 124
private theorem p251 : mobiusTreeCheck cg 1200001 1 728832 d251 = true := by decide +kernel

private abbrev d252 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 125
private theorem p252 : mobiusTreeCheck cg 1200001 1 728896 d252 = true := by decide +kernel

private def d250 : MobiusCertTree := .branch d251 d252
private abbrev d254 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 126
private theorem p254 : mobiusTreeCheck cg 1200001 1 728960 d254 = true := by decide +kernel

private abbrev d255 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock088 127
private theorem p255 : mobiusTreeCheck cg 1200001 1 729024 d255 = true := by decide +kernel

private def d253 : MobiusCertTree := .branch d254 d255
private def d249 : MobiusCertTree := .branch d250 d253
private def d241 : MobiusCertTree := .branch d242 d249
private def d225 : MobiusCertTree := .branch d226 d241
private def d193 : MobiusCertTree := .branch d194 d225
private def d129 : MobiusCertTree := .branch d130 d193
private def d1 : MobiusCertTree := .branch d2 d129
private abbrev d263 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 0
private theorem p263 : mobiusTreeCheck cg 1200001 1 729088 d263 = true := by decide +kernel

private abbrev d264 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 1
private theorem p264 : mobiusTreeCheck cg 1200001 1 729152 d264 = true := by decide +kernel

private def d262 : MobiusCertTree := .branch d263 d264
private abbrev d266 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 2
private theorem p266 : mobiusTreeCheck cg 1200001 1 729216 d266 = true := by decide +kernel

private abbrev d267 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 3
private theorem p267 : mobiusTreeCheck cg 1200001 1 729280 d267 = true := by decide +kernel

private def d265 : MobiusCertTree := .branch d266 d267
private def d261 : MobiusCertTree := .branch d262 d265
private abbrev d270 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 4
private theorem p270 : mobiusTreeCheck cg 1200001 1 729344 d270 = true := by decide +kernel

private abbrev d271 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 5
private theorem p271 : mobiusTreeCheck cg 1200001 1 729408 d271 = true := by decide +kernel

private def d269 : MobiusCertTree := .branch d270 d271
private abbrev d273 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 6
private theorem p273 : mobiusTreeCheck cg 1200001 1 729472 d273 = true := by decide +kernel

private abbrev d274 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 7
private theorem p274 : mobiusTreeCheck cg 1200001 1 729536 d274 = true := by decide +kernel

private def d272 : MobiusCertTree := .branch d273 d274
private def d268 : MobiusCertTree := .branch d269 d272
private def d260 : MobiusCertTree := .branch d261 d268
private abbrev d278 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 8
private theorem p278 : mobiusTreeCheck cg 1200001 1 729600 d278 = true := by decide +kernel

private abbrev d279 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 9
private theorem p279 : mobiusTreeCheck cg 1200001 1 729664 d279 = true := by decide +kernel

private def d277 : MobiusCertTree := .branch d278 d279
private abbrev d281 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 10
private theorem p281 : mobiusTreeCheck cg 1200001 1 729728 d281 = true := by decide +kernel

private abbrev d282 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 11
private theorem p282 : mobiusTreeCheck cg 1200001 1 729792 d282 = true := by decide +kernel

private def d280 : MobiusCertTree := .branch d281 d282
private def d276 : MobiusCertTree := .branch d277 d280
private abbrev d285 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 12
private theorem p285 : mobiusTreeCheck cg 1200001 1 729856 d285 = true := by decide +kernel

private abbrev d286 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 13
private theorem p286 : mobiusTreeCheck cg 1200001 1 729920 d286 = true := by decide +kernel

private def d284 : MobiusCertTree := .branch d285 d286
private abbrev d288 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 14
private theorem p288 : mobiusTreeCheck cg 1200001 1 729984 d288 = true := by decide +kernel

private abbrev d289 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 15
private theorem p289 : mobiusTreeCheck cg 1200001 1 730048 d289 = true := by decide +kernel

private def d287 : MobiusCertTree := .branch d288 d289
private def d283 : MobiusCertTree := .branch d284 d287
private def d275 : MobiusCertTree := .branch d276 d283
private def d259 : MobiusCertTree := .branch d260 d275
private abbrev d294 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 16
private theorem p294 : mobiusTreeCheck cg 1200001 1 730112 d294 = true := by decide +kernel

private abbrev d295 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 17
private theorem p295 : mobiusTreeCheck cg 1200001 1 730176 d295 = true := by decide +kernel

private def d293 : MobiusCertTree := .branch d294 d295
private abbrev d297 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 18
private theorem p297 : mobiusTreeCheck cg 1200001 1 730240 d297 = true := by decide +kernel

private abbrev d298 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 19
private theorem p298 : mobiusTreeCheck cg 1200001 1 730304 d298 = true := by decide +kernel

private def d296 : MobiusCertTree := .branch d297 d298
private def d292 : MobiusCertTree := .branch d293 d296
private abbrev d301 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 20
private theorem p301 : mobiusTreeCheck cg 1200001 1 730368 d301 = true := by decide +kernel

private abbrev d302 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 21
private theorem p302 : mobiusTreeCheck cg 1200001 1 730432 d302 = true := by decide +kernel

private def d300 : MobiusCertTree := .branch d301 d302
private abbrev d304 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 22
private theorem p304 : mobiusTreeCheck cg 1200001 1 730496 d304 = true := by decide +kernel

private abbrev d305 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 23
private theorem p305 : mobiusTreeCheck cg 1200001 1 730560 d305 = true := by decide +kernel

private def d303 : MobiusCertTree := .branch d304 d305
private def d299 : MobiusCertTree := .branch d300 d303
private def d291 : MobiusCertTree := .branch d292 d299
private abbrev d309 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 24
private theorem p309 : mobiusTreeCheck cg 1200001 1 730624 d309 = true := by decide +kernel

private abbrev d310 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 25
private theorem p310 : mobiusTreeCheck cg 1200001 1 730688 d310 = true := by decide +kernel

private def d308 : MobiusCertTree := .branch d309 d310
private abbrev d312 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 26
private theorem p312 : mobiusTreeCheck cg 1200001 1 730752 d312 = true := by decide +kernel

private abbrev d313 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 27
private theorem p313 : mobiusTreeCheck cg 1200001 1 730816 d313 = true := by decide +kernel

private def d311 : MobiusCertTree := .branch d312 d313
private def d307 : MobiusCertTree := .branch d308 d311
private abbrev d316 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 28
private theorem p316 : mobiusTreeCheck cg 1200001 1 730880 d316 = true := by decide +kernel

private abbrev d317 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 29
private theorem p317 : mobiusTreeCheck cg 1200001 1 730944 d317 = true := by decide +kernel

private def d315 : MobiusCertTree := .branch d316 d317
private abbrev d319 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 30
private theorem p319 : mobiusTreeCheck cg 1200001 1 731008 d319 = true := by decide +kernel

private abbrev d320 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 31
private theorem p320 : mobiusTreeCheck cg 1200001 1 731072 d320 = true := by decide +kernel

private def d318 : MobiusCertTree := .branch d319 d320
private def d314 : MobiusCertTree := .branch d315 d318
private def d306 : MobiusCertTree := .branch d307 d314
private def d290 : MobiusCertTree := .branch d291 d306
private def d258 : MobiusCertTree := .branch d259 d290
private abbrev d326 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 32
private theorem p326 : mobiusTreeCheck cg 1200001 1 731136 d326 = true := by decide +kernel

private abbrev d327 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 33
private theorem p327 : mobiusTreeCheck cg 1200001 1 731200 d327 = true := by decide +kernel

private def d325 : MobiusCertTree := .branch d326 d327
private abbrev d329 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 34
private theorem p329 : mobiusTreeCheck cg 1200001 1 731264 d329 = true := by decide +kernel

private abbrev d330 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 35
private theorem p330 : mobiusTreeCheck cg 1200001 1 731328 d330 = true := by decide +kernel

private def d328 : MobiusCertTree := .branch d329 d330
private def d324 : MobiusCertTree := .branch d325 d328
private abbrev d333 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 36
private theorem p333 : mobiusTreeCheck cg 1200001 1 731392 d333 = true := by decide +kernel

private abbrev d334 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 37
private theorem p334 : mobiusTreeCheck cg 1200001 1 731456 d334 = true := by decide +kernel

private def d332 : MobiusCertTree := .branch d333 d334
private abbrev d336 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 38
private theorem p336 : mobiusTreeCheck cg 1200001 1 731520 d336 = true := by decide +kernel

private abbrev d337 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 39
private theorem p337 : mobiusTreeCheck cg 1200001 1 731584 d337 = true := by decide +kernel

private def d335 : MobiusCertTree := .branch d336 d337
private def d331 : MobiusCertTree := .branch d332 d335
private def d323 : MobiusCertTree := .branch d324 d331
private abbrev d341 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 40
private theorem p341 : mobiusTreeCheck cg 1200001 1 731648 d341 = true := by decide +kernel

private abbrev d342 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 41
private theorem p342 : mobiusTreeCheck cg 1200001 1 731712 d342 = true := by decide +kernel

private def d340 : MobiusCertTree := .branch d341 d342
private abbrev d344 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 42
private theorem p344 : mobiusTreeCheck cg 1200001 1 731776 d344 = true := by decide +kernel

private abbrev d345 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 43
private theorem p345 : mobiusTreeCheck cg 1200001 1 731840 d345 = true := by decide +kernel

private def d343 : MobiusCertTree := .branch d344 d345
private def d339 : MobiusCertTree := .branch d340 d343
private abbrev d348 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 44
private theorem p348 : mobiusTreeCheck cg 1200001 1 731904 d348 = true := by decide +kernel

private abbrev d349 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 45
private theorem p349 : mobiusTreeCheck cg 1200001 1 731968 d349 = true := by decide +kernel

private def d347 : MobiusCertTree := .branch d348 d349
private abbrev d351 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 46
private theorem p351 : mobiusTreeCheck cg 1200001 1 732032 d351 = true := by decide +kernel

private abbrev d352 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 47
private theorem p352 : mobiusTreeCheck cg 1200001 1 732096 d352 = true := by decide +kernel

private def d350 : MobiusCertTree := .branch d351 d352
private def d346 : MobiusCertTree := .branch d347 d350
private def d338 : MobiusCertTree := .branch d339 d346
private def d322 : MobiusCertTree := .branch d323 d338
private abbrev d357 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 48
private theorem p357 : mobiusTreeCheck cg 1200001 1 732160 d357 = true := by decide +kernel

private abbrev d358 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 49
private theorem p358 : mobiusTreeCheck cg 1200001 1 732224 d358 = true := by decide +kernel

private def d356 : MobiusCertTree := .branch d357 d358
private abbrev d360 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 50
private theorem p360 : mobiusTreeCheck cg 1200001 1 732288 d360 = true := by decide +kernel

private abbrev d361 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 51
private theorem p361 : mobiusTreeCheck cg 1200001 1 732352 d361 = true := by decide +kernel

private def d359 : MobiusCertTree := .branch d360 d361
private def d355 : MobiusCertTree := .branch d356 d359
private abbrev d364 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 52
private theorem p364 : mobiusTreeCheck cg 1200001 1 732416 d364 = true := by decide +kernel

private abbrev d365 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 53
private theorem p365 : mobiusTreeCheck cg 1200001 1 732480 d365 = true := by decide +kernel

private def d363 : MobiusCertTree := .branch d364 d365
private abbrev d367 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 54
private theorem p367 : mobiusTreeCheck cg 1200001 1 732544 d367 = true := by decide +kernel

private abbrev d368 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 55
private theorem p368 : mobiusTreeCheck cg 1200001 1 732608 d368 = true := by decide +kernel

private def d366 : MobiusCertTree := .branch d367 d368
private def d362 : MobiusCertTree := .branch d363 d366
private def d354 : MobiusCertTree := .branch d355 d362
private abbrev d372 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 56
private theorem p372 : mobiusTreeCheck cg 1200001 1 732672 d372 = true := by decide +kernel

private abbrev d373 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 57
private theorem p373 : mobiusTreeCheck cg 1200001 1 732736 d373 = true := by decide +kernel

private def d371 : MobiusCertTree := .branch d372 d373
private abbrev d375 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 58
private theorem p375 : mobiusTreeCheck cg 1200001 1 732800 d375 = true := by decide +kernel

private abbrev d376 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 59
private theorem p376 : mobiusTreeCheck cg 1200001 1 732864 d376 = true := by decide +kernel

private def d374 : MobiusCertTree := .branch d375 d376
private def d370 : MobiusCertTree := .branch d371 d374
private abbrev d379 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 60
private theorem p379 : mobiusTreeCheck cg 1200001 1 732928 d379 = true := by decide +kernel

private abbrev d380 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 61
private theorem p380 : mobiusTreeCheck cg 1200001 1 732992 d380 = true := by decide +kernel

private def d378 : MobiusCertTree := .branch d379 d380
private abbrev d382 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 62
private theorem p382 : mobiusTreeCheck cg 1200001 1 733056 d382 = true := by decide +kernel

private abbrev d383 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 63
private theorem p383 : mobiusTreeCheck cg 1200001 1 733120 d383 = true := by decide +kernel

private def d381 : MobiusCertTree := .branch d382 d383
private def d377 : MobiusCertTree := .branch d378 d381
private def d369 : MobiusCertTree := .branch d370 d377
private def d353 : MobiusCertTree := .branch d354 d369
private def d321 : MobiusCertTree := .branch d322 d353
private def d257 : MobiusCertTree := .branch d258 d321
private abbrev d390 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 64
private theorem p390 : mobiusTreeCheck cg 1200001 1 733184 d390 = true := by decide +kernel

private abbrev d391 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 65
private theorem p391 : mobiusTreeCheck cg 1200001 1 733248 d391 = true := by decide +kernel

private def d389 : MobiusCertTree := .branch d390 d391
private abbrev d393 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 66
private theorem p393 : mobiusTreeCheck cg 1200001 1 733312 d393 = true := by decide +kernel

private abbrev d394 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 67
private theorem p394 : mobiusTreeCheck cg 1200001 1 733376 d394 = true := by decide +kernel

private def d392 : MobiusCertTree := .branch d393 d394
private def d388 : MobiusCertTree := .branch d389 d392
private abbrev d397 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 68
private theorem p397 : mobiusTreeCheck cg 1200001 1 733440 d397 = true := by decide +kernel

private abbrev d398 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 69
private theorem p398 : mobiusTreeCheck cg 1200001 1 733504 d398 = true := by decide +kernel

private def d396 : MobiusCertTree := .branch d397 d398
private abbrev d400 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 70
private theorem p400 : mobiusTreeCheck cg 1200001 1 733568 d400 = true := by decide +kernel

private abbrev d401 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 71
private theorem p401 : mobiusTreeCheck cg 1200001 1 733632 d401 = true := by decide +kernel

private def d399 : MobiusCertTree := .branch d400 d401
private def d395 : MobiusCertTree := .branch d396 d399
private def d387 : MobiusCertTree := .branch d388 d395
private abbrev d405 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 72
private theorem p405 : mobiusTreeCheck cg 1200001 1 733696 d405 = true := by decide +kernel

private abbrev d406 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 73
private theorem p406 : mobiusTreeCheck cg 1200001 1 733760 d406 = true := by decide +kernel

private def d404 : MobiusCertTree := .branch d405 d406
private abbrev d408 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 74
private theorem p408 : mobiusTreeCheck cg 1200001 1 733824 d408 = true := by decide +kernel

private abbrev d409 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 75
private theorem p409 : mobiusTreeCheck cg 1200001 1 733888 d409 = true := by decide +kernel

private def d407 : MobiusCertTree := .branch d408 d409
private def d403 : MobiusCertTree := .branch d404 d407
private abbrev d412 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 76
private theorem p412 : mobiusTreeCheck cg 1200001 1 733952 d412 = true := by decide +kernel

private abbrev d413 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 77
private theorem p413 : mobiusTreeCheck cg 1200001 1 734016 d413 = true := by decide +kernel

private def d411 : MobiusCertTree := .branch d412 d413
private abbrev d415 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 78
private theorem p415 : mobiusTreeCheck cg 1200001 1 734080 d415 = true := by decide +kernel

private abbrev d416 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 79
private theorem p416 : mobiusTreeCheck cg 1200001 1 734144 d416 = true := by decide +kernel

private def d414 : MobiusCertTree := .branch d415 d416
private def d410 : MobiusCertTree := .branch d411 d414
private def d402 : MobiusCertTree := .branch d403 d410
private def d386 : MobiusCertTree := .branch d387 d402
private abbrev d421 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 80
private theorem p421 : mobiusTreeCheck cg 1200001 1 734208 d421 = true := by decide +kernel

private abbrev d422 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 81
private theorem p422 : mobiusTreeCheck cg 1200001 1 734272 d422 = true := by decide +kernel

private def d420 : MobiusCertTree := .branch d421 d422
private abbrev d424 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 82
private theorem p424 : mobiusTreeCheck cg 1200001 1 734336 d424 = true := by decide +kernel

private abbrev d425 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 83
private theorem p425 : mobiusTreeCheck cg 1200001 1 734400 d425 = true := by decide +kernel

private def d423 : MobiusCertTree := .branch d424 d425
private def d419 : MobiusCertTree := .branch d420 d423
private abbrev d428 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 84
private theorem p428 : mobiusTreeCheck cg 1200001 1 734464 d428 = true := by decide +kernel

private abbrev d429 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 85
private theorem p429 : mobiusTreeCheck cg 1200001 1 734528 d429 = true := by decide +kernel

private def d427 : MobiusCertTree := .branch d428 d429
private abbrev d431 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 86
private theorem p431 : mobiusTreeCheck cg 1200001 1 734592 d431 = true := by decide +kernel

private abbrev d432 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 87
private theorem p432 : mobiusTreeCheck cg 1200001 1 734656 d432 = true := by decide +kernel

private def d430 : MobiusCertTree := .branch d431 d432
private def d426 : MobiusCertTree := .branch d427 d430
private def d418 : MobiusCertTree := .branch d419 d426
private abbrev d436 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 88
private theorem p436 : mobiusTreeCheck cg 1200001 1 734720 d436 = true := by decide +kernel

private abbrev d437 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 89
private theorem p437 : mobiusTreeCheck cg 1200001 1 734784 d437 = true := by decide +kernel

private def d435 : MobiusCertTree := .branch d436 d437
private abbrev d439 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 90
private theorem p439 : mobiusTreeCheck cg 1200001 1 734848 d439 = true := by decide +kernel

private abbrev d440 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 91
private theorem p440 : mobiusTreeCheck cg 1200001 1 734912 d440 = true := by decide +kernel

private def d438 : MobiusCertTree := .branch d439 d440
private def d434 : MobiusCertTree := .branch d435 d438
private abbrev d443 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 92
private theorem p443 : mobiusTreeCheck cg 1200001 1 734976 d443 = true := by decide +kernel

private abbrev d444 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 93
private theorem p444 : mobiusTreeCheck cg 1200001 1 735040 d444 = true := by decide +kernel

private def d442 : MobiusCertTree := .branch d443 d444
private abbrev d446 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 94
private theorem p446 : mobiusTreeCheck cg 1200001 1 735104 d446 = true := by decide +kernel

private abbrev d447 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 95
private theorem p447 : mobiusTreeCheck cg 1200001 1 735168 d447 = true := by decide +kernel

private def d445 : MobiusCertTree := .branch d446 d447
private def d441 : MobiusCertTree := .branch d442 d445
private def d433 : MobiusCertTree := .branch d434 d441
private def d417 : MobiusCertTree := .branch d418 d433
private def d385 : MobiusCertTree := .branch d386 d417
private abbrev d453 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 96
private theorem p453 : mobiusTreeCheck cg 1200001 1 735232 d453 = true := by decide +kernel

private abbrev d454 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 97
private theorem p454 : mobiusTreeCheck cg 1200001 1 735296 d454 = true := by decide +kernel

private def d452 : MobiusCertTree := .branch d453 d454
private abbrev d456 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 98
private theorem p456 : mobiusTreeCheck cg 1200001 1 735360 d456 = true := by decide +kernel

private abbrev d457 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 99
private theorem p457 : mobiusTreeCheck cg 1200001 1 735424 d457 = true := by decide +kernel

private def d455 : MobiusCertTree := .branch d456 d457
private def d451 : MobiusCertTree := .branch d452 d455
private abbrev d460 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 100
private theorem p460 : mobiusTreeCheck cg 1200001 1 735488 d460 = true := by decide +kernel

private abbrev d461 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 101
private theorem p461 : mobiusTreeCheck cg 1200001 1 735552 d461 = true := by decide +kernel

private def d459 : MobiusCertTree := .branch d460 d461
private abbrev d463 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 102
private theorem p463 : mobiusTreeCheck cg 1200001 1 735616 d463 = true := by decide +kernel

private abbrev d464 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 103
private theorem p464 : mobiusTreeCheck cg 1200001 1 735680 d464 = true := by decide +kernel

private def d462 : MobiusCertTree := .branch d463 d464
private def d458 : MobiusCertTree := .branch d459 d462
private def d450 : MobiusCertTree := .branch d451 d458
private abbrev d468 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 104
private theorem p468 : mobiusTreeCheck cg 1200001 1 735744 d468 = true := by decide +kernel

private abbrev d469 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 105
private theorem p469 : mobiusTreeCheck cg 1200001 1 735808 d469 = true := by decide +kernel

private def d467 : MobiusCertTree := .branch d468 d469
private abbrev d471 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 106
private theorem p471 : mobiusTreeCheck cg 1200001 1 735872 d471 = true := by decide +kernel

private abbrev d472 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 107
private theorem p472 : mobiusTreeCheck cg 1200001 1 735936 d472 = true := by decide +kernel

private def d470 : MobiusCertTree := .branch d471 d472
private def d466 : MobiusCertTree := .branch d467 d470
private abbrev d475 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 108
private theorem p475 : mobiusTreeCheck cg 1200001 1 736000 d475 = true := by decide +kernel

private abbrev d476 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 109
private theorem p476 : mobiusTreeCheck cg 1200001 1 736064 d476 = true := by decide +kernel

private def d474 : MobiusCertTree := .branch d475 d476
private abbrev d478 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 110
private theorem p478 : mobiusTreeCheck cg 1200001 1 736128 d478 = true := by decide +kernel

private abbrev d479 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 111
private theorem p479 : mobiusTreeCheck cg 1200001 1 736192 d479 = true := by decide +kernel

private def d477 : MobiusCertTree := .branch d478 d479
private def d473 : MobiusCertTree := .branch d474 d477
private def d465 : MobiusCertTree := .branch d466 d473
private def d449 : MobiusCertTree := .branch d450 d465
private abbrev d484 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 112
private theorem p484 : mobiusTreeCheck cg 1200001 1 736256 d484 = true := by decide +kernel

private abbrev d485 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 113
private theorem p485 : mobiusTreeCheck cg 1200001 1 736320 d485 = true := by decide +kernel

private def d483 : MobiusCertTree := .branch d484 d485
private abbrev d487 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 114
private theorem p487 : mobiusTreeCheck cg 1200001 1 736384 d487 = true := by decide +kernel

private abbrev d488 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 115
private theorem p488 : mobiusTreeCheck cg 1200001 1 736448 d488 = true := by decide +kernel

private def d486 : MobiusCertTree := .branch d487 d488
private def d482 : MobiusCertTree := .branch d483 d486
private abbrev d491 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 116
private theorem p491 : mobiusTreeCheck cg 1200001 1 736512 d491 = true := by decide +kernel

private abbrev d492 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 117
private theorem p492 : mobiusTreeCheck cg 1200001 1 736576 d492 = true := by decide +kernel

private def d490 : MobiusCertTree := .branch d491 d492
private abbrev d494 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 118
private theorem p494 : mobiusTreeCheck cg 1200001 1 736640 d494 = true := by decide +kernel

private abbrev d495 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 119
private theorem p495 : mobiusTreeCheck cg 1200001 1 736704 d495 = true := by decide +kernel

private def d493 : MobiusCertTree := .branch d494 d495
private def d489 : MobiusCertTree := .branch d490 d493
private def d481 : MobiusCertTree := .branch d482 d489
private abbrev d499 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 120
private theorem p499 : mobiusTreeCheck cg 1200001 1 736768 d499 = true := by decide +kernel

private abbrev d500 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 121
private theorem p500 : mobiusTreeCheck cg 1200001 1 736832 d500 = true := by decide +kernel

private def d498 : MobiusCertTree := .branch d499 d500
private abbrev d502 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 122
private theorem p502 : mobiusTreeCheck cg 1200001 1 736896 d502 = true := by decide +kernel

private abbrev d503 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 123
private theorem p503 : mobiusTreeCheck cg 1200001 1 736960 d503 = true := by decide +kernel

private def d501 : MobiusCertTree := .branch d502 d503
private def d497 : MobiusCertTree := .branch d498 d501
private abbrev d506 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 124
private theorem p506 : mobiusTreeCheck cg 1200001 1 737024 d506 = true := by decide +kernel

private abbrev d507 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 125
private theorem p507 : mobiusTreeCheck cg 1200001 1 737088 d507 = true := by decide +kernel

private def d505 : MobiusCertTree := .branch d506 d507
private abbrev d509 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 126
private theorem p509 : mobiusTreeCheck cg 1200001 1 737152 d509 = true := by decide +kernel

private abbrev d510 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock089 127
private theorem p510 : mobiusTreeCheck cg 1200001 1 737216 d510 = true := by decide +kernel

private def d508 : MobiusCertTree := .branch d509 d510
private def d504 : MobiusCertTree := .branch d505 d508
private def d496 : MobiusCertTree := .branch d497 d504
private def d480 : MobiusCertTree := .branch d481 d496
private def d448 : MobiusCertTree := .branch d449 d480
private def d384 : MobiusCertTree := .branch d385 d448
private def d256 : MobiusCertTree := .branch d257 d384
private def d0 : MobiusCertTree := .branch d1 d256

private theorem combined : mobiusTreeCheck cg 1200001 9 720896 d0 = true :=
  (mobiusTreeCheck_join cg 1200001 8 720896 _ _ (mobiusTreeCheck_join cg 1200001 7 720896 _ _ (mobiusTreeCheck_join cg 1200001 6 720896 _ _ (mobiusTreeCheck_join cg 1200001 5 720896 _ _ (mobiusTreeCheck_join cg 1200001 4 720896 _ _ (mobiusTreeCheck_join cg 1200001 3 720896 _ _ (mobiusTreeCheck_join cg 1200001 2 720896 _ _ (mobiusTreeCheck_join cg 1200001 1 720896 _ _ p8 p9) (mobiusTreeCheck_join cg 1200001 1 721024 _ _ p11 p12)) (mobiusTreeCheck_join cg 1200001 2 721152 _ _ (mobiusTreeCheck_join cg 1200001 1 721152 _ _ p15 p16) (mobiusTreeCheck_join cg 1200001 1 721280 _ _ p18 p19))) (mobiusTreeCheck_join cg 1200001 3 721408 _ _ (mobiusTreeCheck_join cg 1200001 2 721408 _ _ (mobiusTreeCheck_join cg 1200001 1 721408 _ _ p23 p24) (mobiusTreeCheck_join cg 1200001 1 721536 _ _ p26 p27)) (mobiusTreeCheck_join cg 1200001 2 721664 _ _ (mobiusTreeCheck_join cg 1200001 1 721664 _ _ p30 p31) (mobiusTreeCheck_join cg 1200001 1 721792 _ _ p33 p34)))) (mobiusTreeCheck_join cg 1200001 4 721920 _ _ (mobiusTreeCheck_join cg 1200001 3 721920 _ _ (mobiusTreeCheck_join cg 1200001 2 721920 _ _ (mobiusTreeCheck_join cg 1200001 1 721920 _ _ p39 p40) (mobiusTreeCheck_join cg 1200001 1 722048 _ _ p42 p43)) (mobiusTreeCheck_join cg 1200001 2 722176 _ _ (mobiusTreeCheck_join cg 1200001 1 722176 _ _ p46 p47) (mobiusTreeCheck_join cg 1200001 1 722304 _ _ p49 p50))) (mobiusTreeCheck_join cg 1200001 3 722432 _ _ (mobiusTreeCheck_join cg 1200001 2 722432 _ _ (mobiusTreeCheck_join cg 1200001 1 722432 _ _ p54 p55) (mobiusTreeCheck_join cg 1200001 1 722560 _ _ p57 p58)) (mobiusTreeCheck_join cg 1200001 2 722688 _ _ (mobiusTreeCheck_join cg 1200001 1 722688 _ _ p61 p62) (mobiusTreeCheck_join cg 1200001 1 722816 _ _ p64 p65))))) (mobiusTreeCheck_join cg 1200001 5 722944 _ _ (mobiusTreeCheck_join cg 1200001 4 722944 _ _ (mobiusTreeCheck_join cg 1200001 3 722944 _ _ (mobiusTreeCheck_join cg 1200001 2 722944 _ _ (mobiusTreeCheck_join cg 1200001 1 722944 _ _ p71 p72) (mobiusTreeCheck_join cg 1200001 1 723072 _ _ p74 p75)) (mobiusTreeCheck_join cg 1200001 2 723200 _ _ (mobiusTreeCheck_join cg 1200001 1 723200 _ _ p78 p79) (mobiusTreeCheck_join cg 1200001 1 723328 _ _ p81 p82))) (mobiusTreeCheck_join cg 1200001 3 723456 _ _ (mobiusTreeCheck_join cg 1200001 2 723456 _ _ (mobiusTreeCheck_join cg 1200001 1 723456 _ _ p86 p87) (mobiusTreeCheck_join cg 1200001 1 723584 _ _ p89 p90)) (mobiusTreeCheck_join cg 1200001 2 723712 _ _ (mobiusTreeCheck_join cg 1200001 1 723712 _ _ p93 p94) (mobiusTreeCheck_join cg 1200001 1 723840 _ _ p96 p97)))) (mobiusTreeCheck_join cg 1200001 4 723968 _ _ (mobiusTreeCheck_join cg 1200001 3 723968 _ _ (mobiusTreeCheck_join cg 1200001 2 723968 _ _ (mobiusTreeCheck_join cg 1200001 1 723968 _ _ p102 p103) (mobiusTreeCheck_join cg 1200001 1 724096 _ _ p105 p106)) (mobiusTreeCheck_join cg 1200001 2 724224 _ _ (mobiusTreeCheck_join cg 1200001 1 724224 _ _ p109 p110) (mobiusTreeCheck_join cg 1200001 1 724352 _ _ p112 p113))) (mobiusTreeCheck_join cg 1200001 3 724480 _ _ (mobiusTreeCheck_join cg 1200001 2 724480 _ _ (mobiusTreeCheck_join cg 1200001 1 724480 _ _ p117 p118) (mobiusTreeCheck_join cg 1200001 1 724608 _ _ p120 p121)) (mobiusTreeCheck_join cg 1200001 2 724736 _ _ (mobiusTreeCheck_join cg 1200001 1 724736 _ _ p124 p125) (mobiusTreeCheck_join cg 1200001 1 724864 _ _ p127 p128)))))) (mobiusTreeCheck_join cg 1200001 6 724992 _ _ (mobiusTreeCheck_join cg 1200001 5 724992 _ _ (mobiusTreeCheck_join cg 1200001 4 724992 _ _ (mobiusTreeCheck_join cg 1200001 3 724992 _ _ (mobiusTreeCheck_join cg 1200001 2 724992 _ _ (mobiusTreeCheck_join cg 1200001 1 724992 _ _ p135 p136) (mobiusTreeCheck_join cg 1200001 1 725120 _ _ p138 p139)) (mobiusTreeCheck_join cg 1200001 2 725248 _ _ (mobiusTreeCheck_join cg 1200001 1 725248 _ _ p142 p143) (mobiusTreeCheck_join cg 1200001 1 725376 _ _ p145 p146))) (mobiusTreeCheck_join cg 1200001 3 725504 _ _ (mobiusTreeCheck_join cg 1200001 2 725504 _ _ (mobiusTreeCheck_join cg 1200001 1 725504 _ _ p150 p151) (mobiusTreeCheck_join cg 1200001 1 725632 _ _ p153 p154)) (mobiusTreeCheck_join cg 1200001 2 725760 _ _ (mobiusTreeCheck_join cg 1200001 1 725760 _ _ p157 p158) (mobiusTreeCheck_join cg 1200001 1 725888 _ _ p160 p161)))) (mobiusTreeCheck_join cg 1200001 4 726016 _ _ (mobiusTreeCheck_join cg 1200001 3 726016 _ _ (mobiusTreeCheck_join cg 1200001 2 726016 _ _ (mobiusTreeCheck_join cg 1200001 1 726016 _ _ p166 p167) (mobiusTreeCheck_join cg 1200001 1 726144 _ _ p169 p170)) (mobiusTreeCheck_join cg 1200001 2 726272 _ _ (mobiusTreeCheck_join cg 1200001 1 726272 _ _ p173 p174) (mobiusTreeCheck_join cg 1200001 1 726400 _ _ p176 p177))) (mobiusTreeCheck_join cg 1200001 3 726528 _ _ (mobiusTreeCheck_join cg 1200001 2 726528 _ _ (mobiusTreeCheck_join cg 1200001 1 726528 _ _ p181 p182) (mobiusTreeCheck_join cg 1200001 1 726656 _ _ p184 p185)) (mobiusTreeCheck_join cg 1200001 2 726784 _ _ (mobiusTreeCheck_join cg 1200001 1 726784 _ _ p188 p189) (mobiusTreeCheck_join cg 1200001 1 726912 _ _ p191 p192))))) (mobiusTreeCheck_join cg 1200001 5 727040 _ _ (mobiusTreeCheck_join cg 1200001 4 727040 _ _ (mobiusTreeCheck_join cg 1200001 3 727040 _ _ (mobiusTreeCheck_join cg 1200001 2 727040 _ _ (mobiusTreeCheck_join cg 1200001 1 727040 _ _ p198 p199) (mobiusTreeCheck_join cg 1200001 1 727168 _ _ p201 p202)) (mobiusTreeCheck_join cg 1200001 2 727296 _ _ (mobiusTreeCheck_join cg 1200001 1 727296 _ _ p205 p206) (mobiusTreeCheck_join cg 1200001 1 727424 _ _ p208 p209))) (mobiusTreeCheck_join cg 1200001 3 727552 _ _ (mobiusTreeCheck_join cg 1200001 2 727552 _ _ (mobiusTreeCheck_join cg 1200001 1 727552 _ _ p213 p214) (mobiusTreeCheck_join cg 1200001 1 727680 _ _ p216 p217)) (mobiusTreeCheck_join cg 1200001 2 727808 _ _ (mobiusTreeCheck_join cg 1200001 1 727808 _ _ p220 p221) (mobiusTreeCheck_join cg 1200001 1 727936 _ _ p223 p224)))) (mobiusTreeCheck_join cg 1200001 4 728064 _ _ (mobiusTreeCheck_join cg 1200001 3 728064 _ _ (mobiusTreeCheck_join cg 1200001 2 728064 _ _ (mobiusTreeCheck_join cg 1200001 1 728064 _ _ p229 p230) (mobiusTreeCheck_join cg 1200001 1 728192 _ _ p232 p233)) (mobiusTreeCheck_join cg 1200001 2 728320 _ _ (mobiusTreeCheck_join cg 1200001 1 728320 _ _ p236 p237) (mobiusTreeCheck_join cg 1200001 1 728448 _ _ p239 p240))) (mobiusTreeCheck_join cg 1200001 3 728576 _ _ (mobiusTreeCheck_join cg 1200001 2 728576 _ _ (mobiusTreeCheck_join cg 1200001 1 728576 _ _ p244 p245) (mobiusTreeCheck_join cg 1200001 1 728704 _ _ p247 p248)) (mobiusTreeCheck_join cg 1200001 2 728832 _ _ (mobiusTreeCheck_join cg 1200001 1 728832 _ _ p251 p252) (mobiusTreeCheck_join cg 1200001 1 728960 _ _ p254 p255))))))) (mobiusTreeCheck_join cg 1200001 7 729088 _ _ (mobiusTreeCheck_join cg 1200001 6 729088 _ _ (mobiusTreeCheck_join cg 1200001 5 729088 _ _ (mobiusTreeCheck_join cg 1200001 4 729088 _ _ (mobiusTreeCheck_join cg 1200001 3 729088 _ _ (mobiusTreeCheck_join cg 1200001 2 729088 _ _ (mobiusTreeCheck_join cg 1200001 1 729088 _ _ p263 p264) (mobiusTreeCheck_join cg 1200001 1 729216 _ _ p266 p267)) (mobiusTreeCheck_join cg 1200001 2 729344 _ _ (mobiusTreeCheck_join cg 1200001 1 729344 _ _ p270 p271) (mobiusTreeCheck_join cg 1200001 1 729472 _ _ p273 p274))) (mobiusTreeCheck_join cg 1200001 3 729600 _ _ (mobiusTreeCheck_join cg 1200001 2 729600 _ _ (mobiusTreeCheck_join cg 1200001 1 729600 _ _ p278 p279) (mobiusTreeCheck_join cg 1200001 1 729728 _ _ p281 p282)) (mobiusTreeCheck_join cg 1200001 2 729856 _ _ (mobiusTreeCheck_join cg 1200001 1 729856 _ _ p285 p286) (mobiusTreeCheck_join cg 1200001 1 729984 _ _ p288 p289)))) (mobiusTreeCheck_join cg 1200001 4 730112 _ _ (mobiusTreeCheck_join cg 1200001 3 730112 _ _ (mobiusTreeCheck_join cg 1200001 2 730112 _ _ (mobiusTreeCheck_join cg 1200001 1 730112 _ _ p294 p295) (mobiusTreeCheck_join cg 1200001 1 730240 _ _ p297 p298)) (mobiusTreeCheck_join cg 1200001 2 730368 _ _ (mobiusTreeCheck_join cg 1200001 1 730368 _ _ p301 p302) (mobiusTreeCheck_join cg 1200001 1 730496 _ _ p304 p305))) (mobiusTreeCheck_join cg 1200001 3 730624 _ _ (mobiusTreeCheck_join cg 1200001 2 730624 _ _ (mobiusTreeCheck_join cg 1200001 1 730624 _ _ p309 p310) (mobiusTreeCheck_join cg 1200001 1 730752 _ _ p312 p313)) (mobiusTreeCheck_join cg 1200001 2 730880 _ _ (mobiusTreeCheck_join cg 1200001 1 730880 _ _ p316 p317) (mobiusTreeCheck_join cg 1200001 1 731008 _ _ p319 p320))))) (mobiusTreeCheck_join cg 1200001 5 731136 _ _ (mobiusTreeCheck_join cg 1200001 4 731136 _ _ (mobiusTreeCheck_join cg 1200001 3 731136 _ _ (mobiusTreeCheck_join cg 1200001 2 731136 _ _ (mobiusTreeCheck_join cg 1200001 1 731136 _ _ p326 p327) (mobiusTreeCheck_join cg 1200001 1 731264 _ _ p329 p330)) (mobiusTreeCheck_join cg 1200001 2 731392 _ _ (mobiusTreeCheck_join cg 1200001 1 731392 _ _ p333 p334) (mobiusTreeCheck_join cg 1200001 1 731520 _ _ p336 p337))) (mobiusTreeCheck_join cg 1200001 3 731648 _ _ (mobiusTreeCheck_join cg 1200001 2 731648 _ _ (mobiusTreeCheck_join cg 1200001 1 731648 _ _ p341 p342) (mobiusTreeCheck_join cg 1200001 1 731776 _ _ p344 p345)) (mobiusTreeCheck_join cg 1200001 2 731904 _ _ (mobiusTreeCheck_join cg 1200001 1 731904 _ _ p348 p349) (mobiusTreeCheck_join cg 1200001 1 732032 _ _ p351 p352)))) (mobiusTreeCheck_join cg 1200001 4 732160 _ _ (mobiusTreeCheck_join cg 1200001 3 732160 _ _ (mobiusTreeCheck_join cg 1200001 2 732160 _ _ (mobiusTreeCheck_join cg 1200001 1 732160 _ _ p357 p358) (mobiusTreeCheck_join cg 1200001 1 732288 _ _ p360 p361)) (mobiusTreeCheck_join cg 1200001 2 732416 _ _ (mobiusTreeCheck_join cg 1200001 1 732416 _ _ p364 p365) (mobiusTreeCheck_join cg 1200001 1 732544 _ _ p367 p368))) (mobiusTreeCheck_join cg 1200001 3 732672 _ _ (mobiusTreeCheck_join cg 1200001 2 732672 _ _ (mobiusTreeCheck_join cg 1200001 1 732672 _ _ p372 p373) (mobiusTreeCheck_join cg 1200001 1 732800 _ _ p375 p376)) (mobiusTreeCheck_join cg 1200001 2 732928 _ _ (mobiusTreeCheck_join cg 1200001 1 732928 _ _ p379 p380) (mobiusTreeCheck_join cg 1200001 1 733056 _ _ p382 p383)))))) (mobiusTreeCheck_join cg 1200001 6 733184 _ _ (mobiusTreeCheck_join cg 1200001 5 733184 _ _ (mobiusTreeCheck_join cg 1200001 4 733184 _ _ (mobiusTreeCheck_join cg 1200001 3 733184 _ _ (mobiusTreeCheck_join cg 1200001 2 733184 _ _ (mobiusTreeCheck_join cg 1200001 1 733184 _ _ p390 p391) (mobiusTreeCheck_join cg 1200001 1 733312 _ _ p393 p394)) (mobiusTreeCheck_join cg 1200001 2 733440 _ _ (mobiusTreeCheck_join cg 1200001 1 733440 _ _ p397 p398) (mobiusTreeCheck_join cg 1200001 1 733568 _ _ p400 p401))) (mobiusTreeCheck_join cg 1200001 3 733696 _ _ (mobiusTreeCheck_join cg 1200001 2 733696 _ _ (mobiusTreeCheck_join cg 1200001 1 733696 _ _ p405 p406) (mobiusTreeCheck_join cg 1200001 1 733824 _ _ p408 p409)) (mobiusTreeCheck_join cg 1200001 2 733952 _ _ (mobiusTreeCheck_join cg 1200001 1 733952 _ _ p412 p413) (mobiusTreeCheck_join cg 1200001 1 734080 _ _ p415 p416)))) (mobiusTreeCheck_join cg 1200001 4 734208 _ _ (mobiusTreeCheck_join cg 1200001 3 734208 _ _ (mobiusTreeCheck_join cg 1200001 2 734208 _ _ (mobiusTreeCheck_join cg 1200001 1 734208 _ _ p421 p422) (mobiusTreeCheck_join cg 1200001 1 734336 _ _ p424 p425)) (mobiusTreeCheck_join cg 1200001 2 734464 _ _ (mobiusTreeCheck_join cg 1200001 1 734464 _ _ p428 p429) (mobiusTreeCheck_join cg 1200001 1 734592 _ _ p431 p432))) (mobiusTreeCheck_join cg 1200001 3 734720 _ _ (mobiusTreeCheck_join cg 1200001 2 734720 _ _ (mobiusTreeCheck_join cg 1200001 1 734720 _ _ p436 p437) (mobiusTreeCheck_join cg 1200001 1 734848 _ _ p439 p440)) (mobiusTreeCheck_join cg 1200001 2 734976 _ _ (mobiusTreeCheck_join cg 1200001 1 734976 _ _ p443 p444) (mobiusTreeCheck_join cg 1200001 1 735104 _ _ p446 p447))))) (mobiusTreeCheck_join cg 1200001 5 735232 _ _ (mobiusTreeCheck_join cg 1200001 4 735232 _ _ (mobiusTreeCheck_join cg 1200001 3 735232 _ _ (mobiusTreeCheck_join cg 1200001 2 735232 _ _ (mobiusTreeCheck_join cg 1200001 1 735232 _ _ p453 p454) (mobiusTreeCheck_join cg 1200001 1 735360 _ _ p456 p457)) (mobiusTreeCheck_join cg 1200001 2 735488 _ _ (mobiusTreeCheck_join cg 1200001 1 735488 _ _ p460 p461) (mobiusTreeCheck_join cg 1200001 1 735616 _ _ p463 p464))) (mobiusTreeCheck_join cg 1200001 3 735744 _ _ (mobiusTreeCheck_join cg 1200001 2 735744 _ _ (mobiusTreeCheck_join cg 1200001 1 735744 _ _ p468 p469) (mobiusTreeCheck_join cg 1200001 1 735872 _ _ p471 p472)) (mobiusTreeCheck_join cg 1200001 2 736000 _ _ (mobiusTreeCheck_join cg 1200001 1 736000 _ _ p475 p476) (mobiusTreeCheck_join cg 1200001 1 736128 _ _ p478 p479)))) (mobiusTreeCheck_join cg 1200001 4 736256 _ _ (mobiusTreeCheck_join cg 1200001 3 736256 _ _ (mobiusTreeCheck_join cg 1200001 2 736256 _ _ (mobiusTreeCheck_join cg 1200001 1 736256 _ _ p484 p485) (mobiusTreeCheck_join cg 1200001 1 736384 _ _ p487 p488)) (mobiusTreeCheck_join cg 1200001 2 736512 _ _ (mobiusTreeCheck_join cg 1200001 1 736512 _ _ p491 p492) (mobiusTreeCheck_join cg 1200001 1 736640 _ _ p494 p495))) (mobiusTreeCheck_join cg 1200001 3 736768 _ _ (mobiusTreeCheck_join cg 1200001 2 736768 _ _ (mobiusTreeCheck_join cg 1200001 1 736768 _ _ p499 p500) (mobiusTreeCheck_join cg 1200001 1 736896 _ _ p502 p503)) (mobiusTreeCheck_join cg 1200001 2 737024 _ _ (mobiusTreeCheck_join cg 1200001 1 737024 _ _ p506 p507) (mobiusTreeCheck_join cg 1200001 1 737152 _ _ p509 p510))))))))

end Helfgott

open Helfgott
theorem solution : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 720896 (MobiusCertTree.branch mobiusTableBlock088 mobiusTableBlock089) = true := Helfgott.combined

#print axioms solution
