-- Prove2me | solution 1 for Helfgott.mobiusValuePair024_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:19:19.445996+00:00
-- url     : https://prove2.me/submissions/ae8f6af0-3148-46fc-9881-3ac47dd61873

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

private abbrev d8 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 0
private theorem p8 : mobiusTreeCheck cg 1200001 1 393216 d8 = true := by decide +kernel

private abbrev d9 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 1
private theorem p9 : mobiusTreeCheck cg 1200001 1 393280 d9 = true := by decide +kernel

private def d7 : MobiusCertTree := .branch d8 d9
private abbrev d11 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 2
private theorem p11 : mobiusTreeCheck cg 1200001 1 393344 d11 = true := by decide +kernel

private abbrev d12 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 3
private theorem p12 : mobiusTreeCheck cg 1200001 1 393408 d12 = true := by decide +kernel

private def d10 : MobiusCertTree := .branch d11 d12
private def d6 : MobiusCertTree := .branch d7 d10
private abbrev d15 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 4
private theorem p15 : mobiusTreeCheck cg 1200001 1 393472 d15 = true := by decide +kernel

private abbrev d16 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 5
private theorem p16 : mobiusTreeCheck cg 1200001 1 393536 d16 = true := by decide +kernel

private def d14 : MobiusCertTree := .branch d15 d16
private abbrev d18 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 6
private theorem p18 : mobiusTreeCheck cg 1200001 1 393600 d18 = true := by decide +kernel

private abbrev d19 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 7
private theorem p19 : mobiusTreeCheck cg 1200001 1 393664 d19 = true := by decide +kernel

private def d17 : MobiusCertTree := .branch d18 d19
private def d13 : MobiusCertTree := .branch d14 d17
private def d5 : MobiusCertTree := .branch d6 d13
private abbrev d23 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 8
private theorem p23 : mobiusTreeCheck cg 1200001 1 393728 d23 = true := by decide +kernel

private abbrev d24 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 9
private theorem p24 : mobiusTreeCheck cg 1200001 1 393792 d24 = true := by decide +kernel

private def d22 : MobiusCertTree := .branch d23 d24
private abbrev d26 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 10
private theorem p26 : mobiusTreeCheck cg 1200001 1 393856 d26 = true := by decide +kernel

private abbrev d27 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 11
private theorem p27 : mobiusTreeCheck cg 1200001 1 393920 d27 = true := by decide +kernel

private def d25 : MobiusCertTree := .branch d26 d27
private def d21 : MobiusCertTree := .branch d22 d25
private abbrev d30 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 12
private theorem p30 : mobiusTreeCheck cg 1200001 1 393984 d30 = true := by decide +kernel

private abbrev d31 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 13
private theorem p31 : mobiusTreeCheck cg 1200001 1 394048 d31 = true := by decide +kernel

private def d29 : MobiusCertTree := .branch d30 d31
private abbrev d33 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 14
private theorem p33 : mobiusTreeCheck cg 1200001 1 394112 d33 = true := by decide +kernel

private abbrev d34 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 15
private theorem p34 : mobiusTreeCheck cg 1200001 1 394176 d34 = true := by decide +kernel

private def d32 : MobiusCertTree := .branch d33 d34
private def d28 : MobiusCertTree := .branch d29 d32
private def d20 : MobiusCertTree := .branch d21 d28
private def d4 : MobiusCertTree := .branch d5 d20
private abbrev d39 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 16
private theorem p39 : mobiusTreeCheck cg 1200001 1 394240 d39 = true := by decide +kernel

private abbrev d40 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 17
private theorem p40 : mobiusTreeCheck cg 1200001 1 394304 d40 = true := by decide +kernel

private def d38 : MobiusCertTree := .branch d39 d40
private abbrev d42 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 18
private theorem p42 : mobiusTreeCheck cg 1200001 1 394368 d42 = true := by decide +kernel

private abbrev d43 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 19
private theorem p43 : mobiusTreeCheck cg 1200001 1 394432 d43 = true := by decide +kernel

private def d41 : MobiusCertTree := .branch d42 d43
private def d37 : MobiusCertTree := .branch d38 d41
private abbrev d46 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 20
private theorem p46 : mobiusTreeCheck cg 1200001 1 394496 d46 = true := by decide +kernel

private abbrev d47 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 21
private theorem p47 : mobiusTreeCheck cg 1200001 1 394560 d47 = true := by decide +kernel

private def d45 : MobiusCertTree := .branch d46 d47
private abbrev d49 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 22
private theorem p49 : mobiusTreeCheck cg 1200001 1 394624 d49 = true := by decide +kernel

private abbrev d50 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 23
private theorem p50 : mobiusTreeCheck cg 1200001 1 394688 d50 = true := by decide +kernel

private def d48 : MobiusCertTree := .branch d49 d50
private def d44 : MobiusCertTree := .branch d45 d48
private def d36 : MobiusCertTree := .branch d37 d44
private abbrev d54 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 24
private theorem p54 : mobiusTreeCheck cg 1200001 1 394752 d54 = true := by decide +kernel

private abbrev d55 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 25
private theorem p55 : mobiusTreeCheck cg 1200001 1 394816 d55 = true := by decide +kernel

private def d53 : MobiusCertTree := .branch d54 d55
private abbrev d57 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 26
private theorem p57 : mobiusTreeCheck cg 1200001 1 394880 d57 = true := by decide +kernel

private abbrev d58 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 27
private theorem p58 : mobiusTreeCheck cg 1200001 1 394944 d58 = true := by decide +kernel

private def d56 : MobiusCertTree := .branch d57 d58
private def d52 : MobiusCertTree := .branch d53 d56
private abbrev d61 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 28
private theorem p61 : mobiusTreeCheck cg 1200001 1 395008 d61 = true := by decide +kernel

private abbrev d62 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 29
private theorem p62 : mobiusTreeCheck cg 1200001 1 395072 d62 = true := by decide +kernel

private def d60 : MobiusCertTree := .branch d61 d62
private abbrev d64 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 30
private theorem p64 : mobiusTreeCheck cg 1200001 1 395136 d64 = true := by decide +kernel

private abbrev d65 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 31
private theorem p65 : mobiusTreeCheck cg 1200001 1 395200 d65 = true := by decide +kernel

private def d63 : MobiusCertTree := .branch d64 d65
private def d59 : MobiusCertTree := .branch d60 d63
private def d51 : MobiusCertTree := .branch d52 d59
private def d35 : MobiusCertTree := .branch d36 d51
private def d3 : MobiusCertTree := .branch d4 d35
private abbrev d71 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 32
private theorem p71 : mobiusTreeCheck cg 1200001 1 395264 d71 = true := by decide +kernel

private abbrev d72 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 33
private theorem p72 : mobiusTreeCheck cg 1200001 1 395328 d72 = true := by decide +kernel

private def d70 : MobiusCertTree := .branch d71 d72
private abbrev d74 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 34
private theorem p74 : mobiusTreeCheck cg 1200001 1 395392 d74 = true := by decide +kernel

private abbrev d75 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 35
private theorem p75 : mobiusTreeCheck cg 1200001 1 395456 d75 = true := by decide +kernel

private def d73 : MobiusCertTree := .branch d74 d75
private def d69 : MobiusCertTree := .branch d70 d73
private abbrev d78 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 36
private theorem p78 : mobiusTreeCheck cg 1200001 1 395520 d78 = true := by decide +kernel

private abbrev d79 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 37
private theorem p79 : mobiusTreeCheck cg 1200001 1 395584 d79 = true := by decide +kernel

private def d77 : MobiusCertTree := .branch d78 d79
private abbrev d81 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 38
private theorem p81 : mobiusTreeCheck cg 1200001 1 395648 d81 = true := by decide +kernel

private abbrev d82 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 39
private theorem p82 : mobiusTreeCheck cg 1200001 1 395712 d82 = true := by decide +kernel

private def d80 : MobiusCertTree := .branch d81 d82
private def d76 : MobiusCertTree := .branch d77 d80
private def d68 : MobiusCertTree := .branch d69 d76
private abbrev d86 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 40
private theorem p86 : mobiusTreeCheck cg 1200001 1 395776 d86 = true := by decide +kernel

private abbrev d87 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 41
private theorem p87 : mobiusTreeCheck cg 1200001 1 395840 d87 = true := by decide +kernel

private def d85 : MobiusCertTree := .branch d86 d87
private abbrev d89 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 42
private theorem p89 : mobiusTreeCheck cg 1200001 1 395904 d89 = true := by decide +kernel

private abbrev d90 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 43
private theorem p90 : mobiusTreeCheck cg 1200001 1 395968 d90 = true := by decide +kernel

private def d88 : MobiusCertTree := .branch d89 d90
private def d84 : MobiusCertTree := .branch d85 d88
private abbrev d93 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 44
private theorem p93 : mobiusTreeCheck cg 1200001 1 396032 d93 = true := by decide +kernel

private abbrev d94 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 45
private theorem p94 : mobiusTreeCheck cg 1200001 1 396096 d94 = true := by decide +kernel

private def d92 : MobiusCertTree := .branch d93 d94
private abbrev d96 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 46
private theorem p96 : mobiusTreeCheck cg 1200001 1 396160 d96 = true := by decide +kernel

private abbrev d97 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 47
private theorem p97 : mobiusTreeCheck cg 1200001 1 396224 d97 = true := by decide +kernel

private def d95 : MobiusCertTree := .branch d96 d97
private def d91 : MobiusCertTree := .branch d92 d95
private def d83 : MobiusCertTree := .branch d84 d91
private def d67 : MobiusCertTree := .branch d68 d83
private abbrev d102 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 48
private theorem p102 : mobiusTreeCheck cg 1200001 1 396288 d102 = true := by decide +kernel

private abbrev d103 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 49
private theorem p103 : mobiusTreeCheck cg 1200001 1 396352 d103 = true := by decide +kernel

private def d101 : MobiusCertTree := .branch d102 d103
private abbrev d105 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 50
private theorem p105 : mobiusTreeCheck cg 1200001 1 396416 d105 = true := by decide +kernel

private abbrev d106 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 51
private theorem p106 : mobiusTreeCheck cg 1200001 1 396480 d106 = true := by decide +kernel

private def d104 : MobiusCertTree := .branch d105 d106
private def d100 : MobiusCertTree := .branch d101 d104
private abbrev d109 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 52
private theorem p109 : mobiusTreeCheck cg 1200001 1 396544 d109 = true := by decide +kernel

private abbrev d110 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 53
private theorem p110 : mobiusTreeCheck cg 1200001 1 396608 d110 = true := by decide +kernel

private def d108 : MobiusCertTree := .branch d109 d110
private abbrev d112 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 54
private theorem p112 : mobiusTreeCheck cg 1200001 1 396672 d112 = true := by decide +kernel

private abbrev d113 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 55
private theorem p113 : mobiusTreeCheck cg 1200001 1 396736 d113 = true := by decide +kernel

private def d111 : MobiusCertTree := .branch d112 d113
private def d107 : MobiusCertTree := .branch d108 d111
private def d99 : MobiusCertTree := .branch d100 d107
private abbrev d117 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 56
private theorem p117 : mobiusTreeCheck cg 1200001 1 396800 d117 = true := by decide +kernel

private abbrev d118 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 57
private theorem p118 : mobiusTreeCheck cg 1200001 1 396864 d118 = true := by decide +kernel

private def d116 : MobiusCertTree := .branch d117 d118
private abbrev d120 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 58
private theorem p120 : mobiusTreeCheck cg 1200001 1 396928 d120 = true := by decide +kernel

private abbrev d121 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 59
private theorem p121 : mobiusTreeCheck cg 1200001 1 396992 d121 = true := by decide +kernel

private def d119 : MobiusCertTree := .branch d120 d121
private def d115 : MobiusCertTree := .branch d116 d119
private abbrev d124 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 60
private theorem p124 : mobiusTreeCheck cg 1200001 1 397056 d124 = true := by decide +kernel

private abbrev d125 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 61
private theorem p125 : mobiusTreeCheck cg 1200001 1 397120 d125 = true := by decide +kernel

private def d123 : MobiusCertTree := .branch d124 d125
private abbrev d127 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 62
private theorem p127 : mobiusTreeCheck cg 1200001 1 397184 d127 = true := by decide +kernel

private abbrev d128 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 63
private theorem p128 : mobiusTreeCheck cg 1200001 1 397248 d128 = true := by decide +kernel

private def d126 : MobiusCertTree := .branch d127 d128
private def d122 : MobiusCertTree := .branch d123 d126
private def d114 : MobiusCertTree := .branch d115 d122
private def d98 : MobiusCertTree := .branch d99 d114
private def d66 : MobiusCertTree := .branch d67 d98
private def d2 : MobiusCertTree := .branch d3 d66
private abbrev d135 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 64
private theorem p135 : mobiusTreeCheck cg 1200001 1 397312 d135 = true := by decide +kernel

private abbrev d136 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 65
private theorem p136 : mobiusTreeCheck cg 1200001 1 397376 d136 = true := by decide +kernel

private def d134 : MobiusCertTree := .branch d135 d136
private abbrev d138 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 66
private theorem p138 : mobiusTreeCheck cg 1200001 1 397440 d138 = true := by decide +kernel

private abbrev d139 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 67
private theorem p139 : mobiusTreeCheck cg 1200001 1 397504 d139 = true := by decide +kernel

private def d137 : MobiusCertTree := .branch d138 d139
private def d133 : MobiusCertTree := .branch d134 d137
private abbrev d142 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 68
private theorem p142 : mobiusTreeCheck cg 1200001 1 397568 d142 = true := by decide +kernel

private abbrev d143 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 69
private theorem p143 : mobiusTreeCheck cg 1200001 1 397632 d143 = true := by decide +kernel

private def d141 : MobiusCertTree := .branch d142 d143
private abbrev d145 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 70
private theorem p145 : mobiusTreeCheck cg 1200001 1 397696 d145 = true := by decide +kernel

private abbrev d146 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 71
private theorem p146 : mobiusTreeCheck cg 1200001 1 397760 d146 = true := by decide +kernel

private def d144 : MobiusCertTree := .branch d145 d146
private def d140 : MobiusCertTree := .branch d141 d144
private def d132 : MobiusCertTree := .branch d133 d140
private abbrev d150 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 72
private theorem p150 : mobiusTreeCheck cg 1200001 1 397824 d150 = true := by decide +kernel

private abbrev d151 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 73
private theorem p151 : mobiusTreeCheck cg 1200001 1 397888 d151 = true := by decide +kernel

private def d149 : MobiusCertTree := .branch d150 d151
private abbrev d153 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 74
private theorem p153 : mobiusTreeCheck cg 1200001 1 397952 d153 = true := by decide +kernel

private abbrev d154 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 75
private theorem p154 : mobiusTreeCheck cg 1200001 1 398016 d154 = true := by decide +kernel

private def d152 : MobiusCertTree := .branch d153 d154
private def d148 : MobiusCertTree := .branch d149 d152
private abbrev d157 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 76
private theorem p157 : mobiusTreeCheck cg 1200001 1 398080 d157 = true := by decide +kernel

private abbrev d158 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 77
private theorem p158 : mobiusTreeCheck cg 1200001 1 398144 d158 = true := by decide +kernel

private def d156 : MobiusCertTree := .branch d157 d158
private abbrev d160 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 78
private theorem p160 : mobiusTreeCheck cg 1200001 1 398208 d160 = true := by decide +kernel

private abbrev d161 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 79
private theorem p161 : mobiusTreeCheck cg 1200001 1 398272 d161 = true := by decide +kernel

private def d159 : MobiusCertTree := .branch d160 d161
private def d155 : MobiusCertTree := .branch d156 d159
private def d147 : MobiusCertTree := .branch d148 d155
private def d131 : MobiusCertTree := .branch d132 d147
private abbrev d166 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 80
private theorem p166 : mobiusTreeCheck cg 1200001 1 398336 d166 = true := by decide +kernel

private abbrev d167 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 81
private theorem p167 : mobiusTreeCheck cg 1200001 1 398400 d167 = true := by decide +kernel

private def d165 : MobiusCertTree := .branch d166 d167
private abbrev d169 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 82
private theorem p169 : mobiusTreeCheck cg 1200001 1 398464 d169 = true := by decide +kernel

private abbrev d170 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 83
private theorem p170 : mobiusTreeCheck cg 1200001 1 398528 d170 = true := by decide +kernel

private def d168 : MobiusCertTree := .branch d169 d170
private def d164 : MobiusCertTree := .branch d165 d168
private abbrev d173 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 84
private theorem p173 : mobiusTreeCheck cg 1200001 1 398592 d173 = true := by decide +kernel

private abbrev d174 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 85
private theorem p174 : mobiusTreeCheck cg 1200001 1 398656 d174 = true := by decide +kernel

private def d172 : MobiusCertTree := .branch d173 d174
private abbrev d176 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 86
private theorem p176 : mobiusTreeCheck cg 1200001 1 398720 d176 = true := by decide +kernel

private abbrev d177 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 87
private theorem p177 : mobiusTreeCheck cg 1200001 1 398784 d177 = true := by decide +kernel

private def d175 : MobiusCertTree := .branch d176 d177
private def d171 : MobiusCertTree := .branch d172 d175
private def d163 : MobiusCertTree := .branch d164 d171
private abbrev d181 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 88
private theorem p181 : mobiusTreeCheck cg 1200001 1 398848 d181 = true := by decide +kernel

private abbrev d182 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 89
private theorem p182 : mobiusTreeCheck cg 1200001 1 398912 d182 = true := by decide +kernel

private def d180 : MobiusCertTree := .branch d181 d182
private abbrev d184 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 90
private theorem p184 : mobiusTreeCheck cg 1200001 1 398976 d184 = true := by decide +kernel

private abbrev d185 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 91
private theorem p185 : mobiusTreeCheck cg 1200001 1 399040 d185 = true := by decide +kernel

private def d183 : MobiusCertTree := .branch d184 d185
private def d179 : MobiusCertTree := .branch d180 d183
private abbrev d188 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 92
private theorem p188 : mobiusTreeCheck cg 1200001 1 399104 d188 = true := by decide +kernel

private abbrev d189 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 93
private theorem p189 : mobiusTreeCheck cg 1200001 1 399168 d189 = true := by decide +kernel

private def d187 : MobiusCertTree := .branch d188 d189
private abbrev d191 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 94
private theorem p191 : mobiusTreeCheck cg 1200001 1 399232 d191 = true := by decide +kernel

private abbrev d192 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 95
private theorem p192 : mobiusTreeCheck cg 1200001 1 399296 d192 = true := by decide +kernel

private def d190 : MobiusCertTree := .branch d191 d192
private def d186 : MobiusCertTree := .branch d187 d190
private def d178 : MobiusCertTree := .branch d179 d186
private def d162 : MobiusCertTree := .branch d163 d178
private def d130 : MobiusCertTree := .branch d131 d162
private abbrev d198 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 96
private theorem p198 : mobiusTreeCheck cg 1200001 1 399360 d198 = true := by decide +kernel

private abbrev d199 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 97
private theorem p199 : mobiusTreeCheck cg 1200001 1 399424 d199 = true := by decide +kernel

private def d197 : MobiusCertTree := .branch d198 d199
private abbrev d201 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 98
private theorem p201 : mobiusTreeCheck cg 1200001 1 399488 d201 = true := by decide +kernel

private abbrev d202 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 99
private theorem p202 : mobiusTreeCheck cg 1200001 1 399552 d202 = true := by decide +kernel

private def d200 : MobiusCertTree := .branch d201 d202
private def d196 : MobiusCertTree := .branch d197 d200
private abbrev d205 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 100
private theorem p205 : mobiusTreeCheck cg 1200001 1 399616 d205 = true := by decide +kernel

private abbrev d206 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 101
private theorem p206 : mobiusTreeCheck cg 1200001 1 399680 d206 = true := by decide +kernel

private def d204 : MobiusCertTree := .branch d205 d206
private abbrev d208 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 102
private theorem p208 : mobiusTreeCheck cg 1200001 1 399744 d208 = true := by decide +kernel

private abbrev d209 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 103
private theorem p209 : mobiusTreeCheck cg 1200001 1 399808 d209 = true := by decide +kernel

private def d207 : MobiusCertTree := .branch d208 d209
private def d203 : MobiusCertTree := .branch d204 d207
private def d195 : MobiusCertTree := .branch d196 d203
private abbrev d213 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 104
private theorem p213 : mobiusTreeCheck cg 1200001 1 399872 d213 = true := by decide +kernel

private abbrev d214 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 105
private theorem p214 : mobiusTreeCheck cg 1200001 1 399936 d214 = true := by decide +kernel

private def d212 : MobiusCertTree := .branch d213 d214
private abbrev d216 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 106
private theorem p216 : mobiusTreeCheck cg 1200001 1 400000 d216 = true := by decide +kernel

private abbrev d217 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 107
private theorem p217 : mobiusTreeCheck cg 1200001 1 400064 d217 = true := by decide +kernel

private def d215 : MobiusCertTree := .branch d216 d217
private def d211 : MobiusCertTree := .branch d212 d215
private abbrev d220 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 108
private theorem p220 : mobiusTreeCheck cg 1200001 1 400128 d220 = true := by decide +kernel

private abbrev d221 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 109
private theorem p221 : mobiusTreeCheck cg 1200001 1 400192 d221 = true := by decide +kernel

private def d219 : MobiusCertTree := .branch d220 d221
private abbrev d223 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 110
private theorem p223 : mobiusTreeCheck cg 1200001 1 400256 d223 = true := by decide +kernel

private abbrev d224 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 111
private theorem p224 : mobiusTreeCheck cg 1200001 1 400320 d224 = true := by decide +kernel

private def d222 : MobiusCertTree := .branch d223 d224
private def d218 : MobiusCertTree := .branch d219 d222
private def d210 : MobiusCertTree := .branch d211 d218
private def d194 : MobiusCertTree := .branch d195 d210
private abbrev d229 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 112
private theorem p229 : mobiusTreeCheck cg 1200001 1 400384 d229 = true := by decide +kernel

private abbrev d230 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 113
private theorem p230 : mobiusTreeCheck cg 1200001 1 400448 d230 = true := by decide +kernel

private def d228 : MobiusCertTree := .branch d229 d230
private abbrev d232 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 114
private theorem p232 : mobiusTreeCheck cg 1200001 1 400512 d232 = true := by decide +kernel

private abbrev d233 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 115
private theorem p233 : mobiusTreeCheck cg 1200001 1 400576 d233 = true := by decide +kernel

private def d231 : MobiusCertTree := .branch d232 d233
private def d227 : MobiusCertTree := .branch d228 d231
private abbrev d236 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 116
private theorem p236 : mobiusTreeCheck cg 1200001 1 400640 d236 = true := by decide +kernel

private abbrev d237 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 117
private theorem p237 : mobiusTreeCheck cg 1200001 1 400704 d237 = true := by decide +kernel

private def d235 : MobiusCertTree := .branch d236 d237
private abbrev d239 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 118
private theorem p239 : mobiusTreeCheck cg 1200001 1 400768 d239 = true := by decide +kernel

private abbrev d240 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 119
private theorem p240 : mobiusTreeCheck cg 1200001 1 400832 d240 = true := by decide +kernel

private def d238 : MobiusCertTree := .branch d239 d240
private def d234 : MobiusCertTree := .branch d235 d238
private def d226 : MobiusCertTree := .branch d227 d234
private abbrev d244 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 120
private theorem p244 : mobiusTreeCheck cg 1200001 1 400896 d244 = true := by decide +kernel

private abbrev d245 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 121
private theorem p245 : mobiusTreeCheck cg 1200001 1 400960 d245 = true := by decide +kernel

private def d243 : MobiusCertTree := .branch d244 d245
private abbrev d247 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 122
private theorem p247 : mobiusTreeCheck cg 1200001 1 401024 d247 = true := by decide +kernel

private abbrev d248 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 123
private theorem p248 : mobiusTreeCheck cg 1200001 1 401088 d248 = true := by decide +kernel

private def d246 : MobiusCertTree := .branch d247 d248
private def d242 : MobiusCertTree := .branch d243 d246
private abbrev d251 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 124
private theorem p251 : mobiusTreeCheck cg 1200001 1 401152 d251 = true := by decide +kernel

private abbrev d252 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 125
private theorem p252 : mobiusTreeCheck cg 1200001 1 401216 d252 = true := by decide +kernel

private def d250 : MobiusCertTree := .branch d251 d252
private abbrev d254 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 126
private theorem p254 : mobiusTreeCheck cg 1200001 1 401280 d254 = true := by decide +kernel

private abbrev d255 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock048 127
private theorem p255 : mobiusTreeCheck cg 1200001 1 401344 d255 = true := by decide +kernel

private def d253 : MobiusCertTree := .branch d254 d255
private def d249 : MobiusCertTree := .branch d250 d253
private def d241 : MobiusCertTree := .branch d242 d249
private def d225 : MobiusCertTree := .branch d226 d241
private def d193 : MobiusCertTree := .branch d194 d225
private def d129 : MobiusCertTree := .branch d130 d193
private def d1 : MobiusCertTree := .branch d2 d129
private abbrev d263 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 0
private theorem p263 : mobiusTreeCheck cg 1200001 1 401408 d263 = true := by decide +kernel

private abbrev d264 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 1
private theorem p264 : mobiusTreeCheck cg 1200001 1 401472 d264 = true := by decide +kernel

private def d262 : MobiusCertTree := .branch d263 d264
private abbrev d266 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 2
private theorem p266 : mobiusTreeCheck cg 1200001 1 401536 d266 = true := by decide +kernel

private abbrev d267 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 3
private theorem p267 : mobiusTreeCheck cg 1200001 1 401600 d267 = true := by decide +kernel

private def d265 : MobiusCertTree := .branch d266 d267
private def d261 : MobiusCertTree := .branch d262 d265
private abbrev d270 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 4
private theorem p270 : mobiusTreeCheck cg 1200001 1 401664 d270 = true := by decide +kernel

private abbrev d271 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 5
private theorem p271 : mobiusTreeCheck cg 1200001 1 401728 d271 = true := by decide +kernel

private def d269 : MobiusCertTree := .branch d270 d271
private abbrev d273 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 6
private theorem p273 : mobiusTreeCheck cg 1200001 1 401792 d273 = true := by decide +kernel

private abbrev d274 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 7
private theorem p274 : mobiusTreeCheck cg 1200001 1 401856 d274 = true := by decide +kernel

private def d272 : MobiusCertTree := .branch d273 d274
private def d268 : MobiusCertTree := .branch d269 d272
private def d260 : MobiusCertTree := .branch d261 d268
private abbrev d278 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 8
private theorem p278 : mobiusTreeCheck cg 1200001 1 401920 d278 = true := by decide +kernel

private abbrev d279 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 9
private theorem p279 : mobiusTreeCheck cg 1200001 1 401984 d279 = true := by decide +kernel

private def d277 : MobiusCertTree := .branch d278 d279
private abbrev d281 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 10
private theorem p281 : mobiusTreeCheck cg 1200001 1 402048 d281 = true := by decide +kernel

private abbrev d282 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 11
private theorem p282 : mobiusTreeCheck cg 1200001 1 402112 d282 = true := by decide +kernel

private def d280 : MobiusCertTree := .branch d281 d282
private def d276 : MobiusCertTree := .branch d277 d280
private abbrev d285 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 12
private theorem p285 : mobiusTreeCheck cg 1200001 1 402176 d285 = true := by decide +kernel

private abbrev d286 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 13
private theorem p286 : mobiusTreeCheck cg 1200001 1 402240 d286 = true := by decide +kernel

private def d284 : MobiusCertTree := .branch d285 d286
private abbrev d288 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 14
private theorem p288 : mobiusTreeCheck cg 1200001 1 402304 d288 = true := by decide +kernel

private abbrev d289 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 15
private theorem p289 : mobiusTreeCheck cg 1200001 1 402368 d289 = true := by decide +kernel

private def d287 : MobiusCertTree := .branch d288 d289
private def d283 : MobiusCertTree := .branch d284 d287
private def d275 : MobiusCertTree := .branch d276 d283
private def d259 : MobiusCertTree := .branch d260 d275
private abbrev d294 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 16
private theorem p294 : mobiusTreeCheck cg 1200001 1 402432 d294 = true := by decide +kernel

private abbrev d295 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 17
private theorem p295 : mobiusTreeCheck cg 1200001 1 402496 d295 = true := by decide +kernel

private def d293 : MobiusCertTree := .branch d294 d295
private abbrev d297 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 18
private theorem p297 : mobiusTreeCheck cg 1200001 1 402560 d297 = true := by decide +kernel

private abbrev d298 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 19
private theorem p298 : mobiusTreeCheck cg 1200001 1 402624 d298 = true := by decide +kernel

private def d296 : MobiusCertTree := .branch d297 d298
private def d292 : MobiusCertTree := .branch d293 d296
private abbrev d301 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 20
private theorem p301 : mobiusTreeCheck cg 1200001 1 402688 d301 = true := by decide +kernel

private abbrev d302 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 21
private theorem p302 : mobiusTreeCheck cg 1200001 1 402752 d302 = true := by decide +kernel

private def d300 : MobiusCertTree := .branch d301 d302
private abbrev d304 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 22
private theorem p304 : mobiusTreeCheck cg 1200001 1 402816 d304 = true := by decide +kernel

private abbrev d305 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 23
private theorem p305 : mobiusTreeCheck cg 1200001 1 402880 d305 = true := by decide +kernel

private def d303 : MobiusCertTree := .branch d304 d305
private def d299 : MobiusCertTree := .branch d300 d303
private def d291 : MobiusCertTree := .branch d292 d299
private abbrev d309 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 24
private theorem p309 : mobiusTreeCheck cg 1200001 1 402944 d309 = true := by decide +kernel

private abbrev d310 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 25
private theorem p310 : mobiusTreeCheck cg 1200001 1 403008 d310 = true := by decide +kernel

private def d308 : MobiusCertTree := .branch d309 d310
private abbrev d312 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 26
private theorem p312 : mobiusTreeCheck cg 1200001 1 403072 d312 = true := by decide +kernel

private abbrev d313 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 27
private theorem p313 : mobiusTreeCheck cg 1200001 1 403136 d313 = true := by decide +kernel

private def d311 : MobiusCertTree := .branch d312 d313
private def d307 : MobiusCertTree := .branch d308 d311
private abbrev d316 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 28
private theorem p316 : mobiusTreeCheck cg 1200001 1 403200 d316 = true := by decide +kernel

private abbrev d317 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 29
private theorem p317 : mobiusTreeCheck cg 1200001 1 403264 d317 = true := by decide +kernel

private def d315 : MobiusCertTree := .branch d316 d317
private abbrev d319 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 30
private theorem p319 : mobiusTreeCheck cg 1200001 1 403328 d319 = true := by decide +kernel

private abbrev d320 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 31
private theorem p320 : mobiusTreeCheck cg 1200001 1 403392 d320 = true := by decide +kernel

private def d318 : MobiusCertTree := .branch d319 d320
private def d314 : MobiusCertTree := .branch d315 d318
private def d306 : MobiusCertTree := .branch d307 d314
private def d290 : MobiusCertTree := .branch d291 d306
private def d258 : MobiusCertTree := .branch d259 d290
private abbrev d326 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 32
private theorem p326 : mobiusTreeCheck cg 1200001 1 403456 d326 = true := by decide +kernel

private abbrev d327 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 33
private theorem p327 : mobiusTreeCheck cg 1200001 1 403520 d327 = true := by decide +kernel

private def d325 : MobiusCertTree := .branch d326 d327
private abbrev d329 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 34
private theorem p329 : mobiusTreeCheck cg 1200001 1 403584 d329 = true := by decide +kernel

private abbrev d330 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 35
private theorem p330 : mobiusTreeCheck cg 1200001 1 403648 d330 = true := by decide +kernel

private def d328 : MobiusCertTree := .branch d329 d330
private def d324 : MobiusCertTree := .branch d325 d328
private abbrev d333 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 36
private theorem p333 : mobiusTreeCheck cg 1200001 1 403712 d333 = true := by decide +kernel

private abbrev d334 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 37
private theorem p334 : mobiusTreeCheck cg 1200001 1 403776 d334 = true := by decide +kernel

private def d332 : MobiusCertTree := .branch d333 d334
private abbrev d336 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 38
private theorem p336 : mobiusTreeCheck cg 1200001 1 403840 d336 = true := by decide +kernel

private abbrev d337 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 39
private theorem p337 : mobiusTreeCheck cg 1200001 1 403904 d337 = true := by decide +kernel

private def d335 : MobiusCertTree := .branch d336 d337
private def d331 : MobiusCertTree := .branch d332 d335
private def d323 : MobiusCertTree := .branch d324 d331
private abbrev d341 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 40
private theorem p341 : mobiusTreeCheck cg 1200001 1 403968 d341 = true := by decide +kernel

private abbrev d342 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 41
private theorem p342 : mobiusTreeCheck cg 1200001 1 404032 d342 = true := by decide +kernel

private def d340 : MobiusCertTree := .branch d341 d342
private abbrev d344 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 42
private theorem p344 : mobiusTreeCheck cg 1200001 1 404096 d344 = true := by decide +kernel

private abbrev d345 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 43
private theorem p345 : mobiusTreeCheck cg 1200001 1 404160 d345 = true := by decide +kernel

private def d343 : MobiusCertTree := .branch d344 d345
private def d339 : MobiusCertTree := .branch d340 d343
private abbrev d348 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 44
private theorem p348 : mobiusTreeCheck cg 1200001 1 404224 d348 = true := by decide +kernel

private abbrev d349 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 45
private theorem p349 : mobiusTreeCheck cg 1200001 1 404288 d349 = true := by decide +kernel

private def d347 : MobiusCertTree := .branch d348 d349
private abbrev d351 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 46
private theorem p351 : mobiusTreeCheck cg 1200001 1 404352 d351 = true := by decide +kernel

private abbrev d352 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 47
private theorem p352 : mobiusTreeCheck cg 1200001 1 404416 d352 = true := by decide +kernel

private def d350 : MobiusCertTree := .branch d351 d352
private def d346 : MobiusCertTree := .branch d347 d350
private def d338 : MobiusCertTree := .branch d339 d346
private def d322 : MobiusCertTree := .branch d323 d338
private abbrev d357 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 48
private theorem p357 : mobiusTreeCheck cg 1200001 1 404480 d357 = true := by decide +kernel

private abbrev d358 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 49
private theorem p358 : mobiusTreeCheck cg 1200001 1 404544 d358 = true := by decide +kernel

private def d356 : MobiusCertTree := .branch d357 d358
private abbrev d360 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 50
private theorem p360 : mobiusTreeCheck cg 1200001 1 404608 d360 = true := by decide +kernel

private abbrev d361 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 51
private theorem p361 : mobiusTreeCheck cg 1200001 1 404672 d361 = true := by decide +kernel

private def d359 : MobiusCertTree := .branch d360 d361
private def d355 : MobiusCertTree := .branch d356 d359
private abbrev d364 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 52
private theorem p364 : mobiusTreeCheck cg 1200001 1 404736 d364 = true := by decide +kernel

private abbrev d365 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 53
private theorem p365 : mobiusTreeCheck cg 1200001 1 404800 d365 = true := by decide +kernel

private def d363 : MobiusCertTree := .branch d364 d365
private abbrev d367 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 54
private theorem p367 : mobiusTreeCheck cg 1200001 1 404864 d367 = true := by decide +kernel

private abbrev d368 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 55
private theorem p368 : mobiusTreeCheck cg 1200001 1 404928 d368 = true := by decide +kernel

private def d366 : MobiusCertTree := .branch d367 d368
private def d362 : MobiusCertTree := .branch d363 d366
private def d354 : MobiusCertTree := .branch d355 d362
private abbrev d372 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 56
private theorem p372 : mobiusTreeCheck cg 1200001 1 404992 d372 = true := by decide +kernel

private abbrev d373 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 57
private theorem p373 : mobiusTreeCheck cg 1200001 1 405056 d373 = true := by decide +kernel

private def d371 : MobiusCertTree := .branch d372 d373
private abbrev d375 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 58
private theorem p375 : mobiusTreeCheck cg 1200001 1 405120 d375 = true := by decide +kernel

private abbrev d376 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 59
private theorem p376 : mobiusTreeCheck cg 1200001 1 405184 d376 = true := by decide +kernel

private def d374 : MobiusCertTree := .branch d375 d376
private def d370 : MobiusCertTree := .branch d371 d374
private abbrev d379 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 60
private theorem p379 : mobiusTreeCheck cg 1200001 1 405248 d379 = true := by decide +kernel

private abbrev d380 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 61
private theorem p380 : mobiusTreeCheck cg 1200001 1 405312 d380 = true := by decide +kernel

private def d378 : MobiusCertTree := .branch d379 d380
private abbrev d382 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 62
private theorem p382 : mobiusTreeCheck cg 1200001 1 405376 d382 = true := by decide +kernel

private abbrev d383 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 63
private theorem p383 : mobiusTreeCheck cg 1200001 1 405440 d383 = true := by decide +kernel

private def d381 : MobiusCertTree := .branch d382 d383
private def d377 : MobiusCertTree := .branch d378 d381
private def d369 : MobiusCertTree := .branch d370 d377
private def d353 : MobiusCertTree := .branch d354 d369
private def d321 : MobiusCertTree := .branch d322 d353
private def d257 : MobiusCertTree := .branch d258 d321
private abbrev d390 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 64
private theorem p390 : mobiusTreeCheck cg 1200001 1 405504 d390 = true := by decide +kernel

private abbrev d391 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 65
private theorem p391 : mobiusTreeCheck cg 1200001 1 405568 d391 = true := by decide +kernel

private def d389 : MobiusCertTree := .branch d390 d391
private abbrev d393 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 66
private theorem p393 : mobiusTreeCheck cg 1200001 1 405632 d393 = true := by decide +kernel

private abbrev d394 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 67
private theorem p394 : mobiusTreeCheck cg 1200001 1 405696 d394 = true := by decide +kernel

private def d392 : MobiusCertTree := .branch d393 d394
private def d388 : MobiusCertTree := .branch d389 d392
private abbrev d397 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 68
private theorem p397 : mobiusTreeCheck cg 1200001 1 405760 d397 = true := by decide +kernel

private abbrev d398 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 69
private theorem p398 : mobiusTreeCheck cg 1200001 1 405824 d398 = true := by decide +kernel

private def d396 : MobiusCertTree := .branch d397 d398
private abbrev d400 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 70
private theorem p400 : mobiusTreeCheck cg 1200001 1 405888 d400 = true := by decide +kernel

private abbrev d401 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 71
private theorem p401 : mobiusTreeCheck cg 1200001 1 405952 d401 = true := by decide +kernel

private def d399 : MobiusCertTree := .branch d400 d401
private def d395 : MobiusCertTree := .branch d396 d399
private def d387 : MobiusCertTree := .branch d388 d395
private abbrev d405 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 72
private theorem p405 : mobiusTreeCheck cg 1200001 1 406016 d405 = true := by decide +kernel

private abbrev d406 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 73
private theorem p406 : mobiusTreeCheck cg 1200001 1 406080 d406 = true := by decide +kernel

private def d404 : MobiusCertTree := .branch d405 d406
private abbrev d408 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 74
private theorem p408 : mobiusTreeCheck cg 1200001 1 406144 d408 = true := by decide +kernel

private abbrev d409 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 75
private theorem p409 : mobiusTreeCheck cg 1200001 1 406208 d409 = true := by decide +kernel

private def d407 : MobiusCertTree := .branch d408 d409
private def d403 : MobiusCertTree := .branch d404 d407
private abbrev d412 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 76
private theorem p412 : mobiusTreeCheck cg 1200001 1 406272 d412 = true := by decide +kernel

private abbrev d413 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 77
private theorem p413 : mobiusTreeCheck cg 1200001 1 406336 d413 = true := by decide +kernel

private def d411 : MobiusCertTree := .branch d412 d413
private abbrev d415 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 78
private theorem p415 : mobiusTreeCheck cg 1200001 1 406400 d415 = true := by decide +kernel

private abbrev d416 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 79
private theorem p416 : mobiusTreeCheck cg 1200001 1 406464 d416 = true := by decide +kernel

private def d414 : MobiusCertTree := .branch d415 d416
private def d410 : MobiusCertTree := .branch d411 d414
private def d402 : MobiusCertTree := .branch d403 d410
private def d386 : MobiusCertTree := .branch d387 d402
private abbrev d421 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 80
private theorem p421 : mobiusTreeCheck cg 1200001 1 406528 d421 = true := by decide +kernel

private abbrev d422 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 81
private theorem p422 : mobiusTreeCheck cg 1200001 1 406592 d422 = true := by decide +kernel

private def d420 : MobiusCertTree := .branch d421 d422
private abbrev d424 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 82
private theorem p424 : mobiusTreeCheck cg 1200001 1 406656 d424 = true := by decide +kernel

private abbrev d425 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 83
private theorem p425 : mobiusTreeCheck cg 1200001 1 406720 d425 = true := by decide +kernel

private def d423 : MobiusCertTree := .branch d424 d425
private def d419 : MobiusCertTree := .branch d420 d423
private abbrev d428 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 84
private theorem p428 : mobiusTreeCheck cg 1200001 1 406784 d428 = true := by decide +kernel

private abbrev d429 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 85
private theorem p429 : mobiusTreeCheck cg 1200001 1 406848 d429 = true := by decide +kernel

private def d427 : MobiusCertTree := .branch d428 d429
private abbrev d431 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 86
private theorem p431 : mobiusTreeCheck cg 1200001 1 406912 d431 = true := by decide +kernel

private abbrev d432 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 87
private theorem p432 : mobiusTreeCheck cg 1200001 1 406976 d432 = true := by decide +kernel

private def d430 : MobiusCertTree := .branch d431 d432
private def d426 : MobiusCertTree := .branch d427 d430
private def d418 : MobiusCertTree := .branch d419 d426
private abbrev d436 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 88
private theorem p436 : mobiusTreeCheck cg 1200001 1 407040 d436 = true := by decide +kernel

private abbrev d437 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 89
private theorem p437 : mobiusTreeCheck cg 1200001 1 407104 d437 = true := by decide +kernel

private def d435 : MobiusCertTree := .branch d436 d437
private abbrev d439 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 90
private theorem p439 : mobiusTreeCheck cg 1200001 1 407168 d439 = true := by decide +kernel

private abbrev d440 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 91
private theorem p440 : mobiusTreeCheck cg 1200001 1 407232 d440 = true := by decide +kernel

private def d438 : MobiusCertTree := .branch d439 d440
private def d434 : MobiusCertTree := .branch d435 d438
private abbrev d443 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 92
private theorem p443 : mobiusTreeCheck cg 1200001 1 407296 d443 = true := by decide +kernel

private abbrev d444 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 93
private theorem p444 : mobiusTreeCheck cg 1200001 1 407360 d444 = true := by decide +kernel

private def d442 : MobiusCertTree := .branch d443 d444
private abbrev d446 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 94
private theorem p446 : mobiusTreeCheck cg 1200001 1 407424 d446 = true := by decide +kernel

private abbrev d447 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 95
private theorem p447 : mobiusTreeCheck cg 1200001 1 407488 d447 = true := by decide +kernel

private def d445 : MobiusCertTree := .branch d446 d447
private def d441 : MobiusCertTree := .branch d442 d445
private def d433 : MobiusCertTree := .branch d434 d441
private def d417 : MobiusCertTree := .branch d418 d433
private def d385 : MobiusCertTree := .branch d386 d417
private abbrev d453 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 96
private theorem p453 : mobiusTreeCheck cg 1200001 1 407552 d453 = true := by decide +kernel

private abbrev d454 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 97
private theorem p454 : mobiusTreeCheck cg 1200001 1 407616 d454 = true := by decide +kernel

private def d452 : MobiusCertTree := .branch d453 d454
private abbrev d456 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 98
private theorem p456 : mobiusTreeCheck cg 1200001 1 407680 d456 = true := by decide +kernel

private abbrev d457 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 99
private theorem p457 : mobiusTreeCheck cg 1200001 1 407744 d457 = true := by decide +kernel

private def d455 : MobiusCertTree := .branch d456 d457
private def d451 : MobiusCertTree := .branch d452 d455
private abbrev d460 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 100
private theorem p460 : mobiusTreeCheck cg 1200001 1 407808 d460 = true := by decide +kernel

private abbrev d461 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 101
private theorem p461 : mobiusTreeCheck cg 1200001 1 407872 d461 = true := by decide +kernel

private def d459 : MobiusCertTree := .branch d460 d461
private abbrev d463 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 102
private theorem p463 : mobiusTreeCheck cg 1200001 1 407936 d463 = true := by decide +kernel

private abbrev d464 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 103
private theorem p464 : mobiusTreeCheck cg 1200001 1 408000 d464 = true := by decide +kernel

private def d462 : MobiusCertTree := .branch d463 d464
private def d458 : MobiusCertTree := .branch d459 d462
private def d450 : MobiusCertTree := .branch d451 d458
private abbrev d468 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 104
private theorem p468 : mobiusTreeCheck cg 1200001 1 408064 d468 = true := by decide +kernel

private abbrev d469 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 105
private theorem p469 : mobiusTreeCheck cg 1200001 1 408128 d469 = true := by decide +kernel

private def d467 : MobiusCertTree := .branch d468 d469
private abbrev d471 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 106
private theorem p471 : mobiusTreeCheck cg 1200001 1 408192 d471 = true := by decide +kernel

private abbrev d472 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 107
private theorem p472 : mobiusTreeCheck cg 1200001 1 408256 d472 = true := by decide +kernel

private def d470 : MobiusCertTree := .branch d471 d472
private def d466 : MobiusCertTree := .branch d467 d470
private abbrev d475 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 108
private theorem p475 : mobiusTreeCheck cg 1200001 1 408320 d475 = true := by decide +kernel

private abbrev d476 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 109
private theorem p476 : mobiusTreeCheck cg 1200001 1 408384 d476 = true := by decide +kernel

private def d474 : MobiusCertTree := .branch d475 d476
private abbrev d478 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 110
private theorem p478 : mobiusTreeCheck cg 1200001 1 408448 d478 = true := by decide +kernel

private abbrev d479 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 111
private theorem p479 : mobiusTreeCheck cg 1200001 1 408512 d479 = true := by decide +kernel

private def d477 : MobiusCertTree := .branch d478 d479
private def d473 : MobiusCertTree := .branch d474 d477
private def d465 : MobiusCertTree := .branch d466 d473
private def d449 : MobiusCertTree := .branch d450 d465
private abbrev d484 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 112
private theorem p484 : mobiusTreeCheck cg 1200001 1 408576 d484 = true := by decide +kernel

private abbrev d485 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 113
private theorem p485 : mobiusTreeCheck cg 1200001 1 408640 d485 = true := by decide +kernel

private def d483 : MobiusCertTree := .branch d484 d485
private abbrev d487 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 114
private theorem p487 : mobiusTreeCheck cg 1200001 1 408704 d487 = true := by decide +kernel

private abbrev d488 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 115
private theorem p488 : mobiusTreeCheck cg 1200001 1 408768 d488 = true := by decide +kernel

private def d486 : MobiusCertTree := .branch d487 d488
private def d482 : MobiusCertTree := .branch d483 d486
private abbrev d491 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 116
private theorem p491 : mobiusTreeCheck cg 1200001 1 408832 d491 = true := by decide +kernel

private abbrev d492 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 117
private theorem p492 : mobiusTreeCheck cg 1200001 1 408896 d492 = true := by decide +kernel

private def d490 : MobiusCertTree := .branch d491 d492
private abbrev d494 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 118
private theorem p494 : mobiusTreeCheck cg 1200001 1 408960 d494 = true := by decide +kernel

private abbrev d495 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 119
private theorem p495 : mobiusTreeCheck cg 1200001 1 409024 d495 = true := by decide +kernel

private def d493 : MobiusCertTree := .branch d494 d495
private def d489 : MobiusCertTree := .branch d490 d493
private def d481 : MobiusCertTree := .branch d482 d489
private abbrev d499 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 120
private theorem p499 : mobiusTreeCheck cg 1200001 1 409088 d499 = true := by decide +kernel

private abbrev d500 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 121
private theorem p500 : mobiusTreeCheck cg 1200001 1 409152 d500 = true := by decide +kernel

private def d498 : MobiusCertTree := .branch d499 d500
private abbrev d502 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 122
private theorem p502 : mobiusTreeCheck cg 1200001 1 409216 d502 = true := by decide +kernel

private abbrev d503 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 123
private theorem p503 : mobiusTreeCheck cg 1200001 1 409280 d503 = true := by decide +kernel

private def d501 : MobiusCertTree := .branch d502 d503
private def d497 : MobiusCertTree := .branch d498 d501
private abbrev d506 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 124
private theorem p506 : mobiusTreeCheck cg 1200001 1 409344 d506 = true := by decide +kernel

private abbrev d507 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 125
private theorem p507 : mobiusTreeCheck cg 1200001 1 409408 d507 = true := by decide +kernel

private def d505 : MobiusCertTree := .branch d506 d507
private abbrev d509 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 126
private theorem p509 : mobiusTreeCheck cg 1200001 1 409472 d509 = true := by decide +kernel

private abbrev d510 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock049 127
private theorem p510 : mobiusTreeCheck cg 1200001 1 409536 d510 = true := by decide +kernel

private def d508 : MobiusCertTree := .branch d509 d510
private def d504 : MobiusCertTree := .branch d505 d508
private def d496 : MobiusCertTree := .branch d497 d504
private def d480 : MobiusCertTree := .branch d481 d496
private def d448 : MobiusCertTree := .branch d449 d480
private def d384 : MobiusCertTree := .branch d385 d448
private def d256 : MobiusCertTree := .branch d257 d384
private def d0 : MobiusCertTree := .branch d1 d256

private theorem combined : mobiusTreeCheck cg 1200001 9 393216 d0 = true :=
  (mobiusTreeCheck_join cg 1200001 8 393216 _ _ (mobiusTreeCheck_join cg 1200001 7 393216 _ _ (mobiusTreeCheck_join cg 1200001 6 393216 _ _ (mobiusTreeCheck_join cg 1200001 5 393216 _ _ (mobiusTreeCheck_join cg 1200001 4 393216 _ _ (mobiusTreeCheck_join cg 1200001 3 393216 _ _ (mobiusTreeCheck_join cg 1200001 2 393216 _ _ (mobiusTreeCheck_join cg 1200001 1 393216 _ _ p8 p9) (mobiusTreeCheck_join cg 1200001 1 393344 _ _ p11 p12)) (mobiusTreeCheck_join cg 1200001 2 393472 _ _ (mobiusTreeCheck_join cg 1200001 1 393472 _ _ p15 p16) (mobiusTreeCheck_join cg 1200001 1 393600 _ _ p18 p19))) (mobiusTreeCheck_join cg 1200001 3 393728 _ _ (mobiusTreeCheck_join cg 1200001 2 393728 _ _ (mobiusTreeCheck_join cg 1200001 1 393728 _ _ p23 p24) (mobiusTreeCheck_join cg 1200001 1 393856 _ _ p26 p27)) (mobiusTreeCheck_join cg 1200001 2 393984 _ _ (mobiusTreeCheck_join cg 1200001 1 393984 _ _ p30 p31) (mobiusTreeCheck_join cg 1200001 1 394112 _ _ p33 p34)))) (mobiusTreeCheck_join cg 1200001 4 394240 _ _ (mobiusTreeCheck_join cg 1200001 3 394240 _ _ (mobiusTreeCheck_join cg 1200001 2 394240 _ _ (mobiusTreeCheck_join cg 1200001 1 394240 _ _ p39 p40) (mobiusTreeCheck_join cg 1200001 1 394368 _ _ p42 p43)) (mobiusTreeCheck_join cg 1200001 2 394496 _ _ (mobiusTreeCheck_join cg 1200001 1 394496 _ _ p46 p47) (mobiusTreeCheck_join cg 1200001 1 394624 _ _ p49 p50))) (mobiusTreeCheck_join cg 1200001 3 394752 _ _ (mobiusTreeCheck_join cg 1200001 2 394752 _ _ (mobiusTreeCheck_join cg 1200001 1 394752 _ _ p54 p55) (mobiusTreeCheck_join cg 1200001 1 394880 _ _ p57 p58)) (mobiusTreeCheck_join cg 1200001 2 395008 _ _ (mobiusTreeCheck_join cg 1200001 1 395008 _ _ p61 p62) (mobiusTreeCheck_join cg 1200001 1 395136 _ _ p64 p65))))) (mobiusTreeCheck_join cg 1200001 5 395264 _ _ (mobiusTreeCheck_join cg 1200001 4 395264 _ _ (mobiusTreeCheck_join cg 1200001 3 395264 _ _ (mobiusTreeCheck_join cg 1200001 2 395264 _ _ (mobiusTreeCheck_join cg 1200001 1 395264 _ _ p71 p72) (mobiusTreeCheck_join cg 1200001 1 395392 _ _ p74 p75)) (mobiusTreeCheck_join cg 1200001 2 395520 _ _ (mobiusTreeCheck_join cg 1200001 1 395520 _ _ p78 p79) (mobiusTreeCheck_join cg 1200001 1 395648 _ _ p81 p82))) (mobiusTreeCheck_join cg 1200001 3 395776 _ _ (mobiusTreeCheck_join cg 1200001 2 395776 _ _ (mobiusTreeCheck_join cg 1200001 1 395776 _ _ p86 p87) (mobiusTreeCheck_join cg 1200001 1 395904 _ _ p89 p90)) (mobiusTreeCheck_join cg 1200001 2 396032 _ _ (mobiusTreeCheck_join cg 1200001 1 396032 _ _ p93 p94) (mobiusTreeCheck_join cg 1200001 1 396160 _ _ p96 p97)))) (mobiusTreeCheck_join cg 1200001 4 396288 _ _ (mobiusTreeCheck_join cg 1200001 3 396288 _ _ (mobiusTreeCheck_join cg 1200001 2 396288 _ _ (mobiusTreeCheck_join cg 1200001 1 396288 _ _ p102 p103) (mobiusTreeCheck_join cg 1200001 1 396416 _ _ p105 p106)) (mobiusTreeCheck_join cg 1200001 2 396544 _ _ (mobiusTreeCheck_join cg 1200001 1 396544 _ _ p109 p110) (mobiusTreeCheck_join cg 1200001 1 396672 _ _ p112 p113))) (mobiusTreeCheck_join cg 1200001 3 396800 _ _ (mobiusTreeCheck_join cg 1200001 2 396800 _ _ (mobiusTreeCheck_join cg 1200001 1 396800 _ _ p117 p118) (mobiusTreeCheck_join cg 1200001 1 396928 _ _ p120 p121)) (mobiusTreeCheck_join cg 1200001 2 397056 _ _ (mobiusTreeCheck_join cg 1200001 1 397056 _ _ p124 p125) (mobiusTreeCheck_join cg 1200001 1 397184 _ _ p127 p128)))))) (mobiusTreeCheck_join cg 1200001 6 397312 _ _ (mobiusTreeCheck_join cg 1200001 5 397312 _ _ (mobiusTreeCheck_join cg 1200001 4 397312 _ _ (mobiusTreeCheck_join cg 1200001 3 397312 _ _ (mobiusTreeCheck_join cg 1200001 2 397312 _ _ (mobiusTreeCheck_join cg 1200001 1 397312 _ _ p135 p136) (mobiusTreeCheck_join cg 1200001 1 397440 _ _ p138 p139)) (mobiusTreeCheck_join cg 1200001 2 397568 _ _ (mobiusTreeCheck_join cg 1200001 1 397568 _ _ p142 p143) (mobiusTreeCheck_join cg 1200001 1 397696 _ _ p145 p146))) (mobiusTreeCheck_join cg 1200001 3 397824 _ _ (mobiusTreeCheck_join cg 1200001 2 397824 _ _ (mobiusTreeCheck_join cg 1200001 1 397824 _ _ p150 p151) (mobiusTreeCheck_join cg 1200001 1 397952 _ _ p153 p154)) (mobiusTreeCheck_join cg 1200001 2 398080 _ _ (mobiusTreeCheck_join cg 1200001 1 398080 _ _ p157 p158) (mobiusTreeCheck_join cg 1200001 1 398208 _ _ p160 p161)))) (mobiusTreeCheck_join cg 1200001 4 398336 _ _ (mobiusTreeCheck_join cg 1200001 3 398336 _ _ (mobiusTreeCheck_join cg 1200001 2 398336 _ _ (mobiusTreeCheck_join cg 1200001 1 398336 _ _ p166 p167) (mobiusTreeCheck_join cg 1200001 1 398464 _ _ p169 p170)) (mobiusTreeCheck_join cg 1200001 2 398592 _ _ (mobiusTreeCheck_join cg 1200001 1 398592 _ _ p173 p174) (mobiusTreeCheck_join cg 1200001 1 398720 _ _ p176 p177))) (mobiusTreeCheck_join cg 1200001 3 398848 _ _ (mobiusTreeCheck_join cg 1200001 2 398848 _ _ (mobiusTreeCheck_join cg 1200001 1 398848 _ _ p181 p182) (mobiusTreeCheck_join cg 1200001 1 398976 _ _ p184 p185)) (mobiusTreeCheck_join cg 1200001 2 399104 _ _ (mobiusTreeCheck_join cg 1200001 1 399104 _ _ p188 p189) (mobiusTreeCheck_join cg 1200001 1 399232 _ _ p191 p192))))) (mobiusTreeCheck_join cg 1200001 5 399360 _ _ (mobiusTreeCheck_join cg 1200001 4 399360 _ _ (mobiusTreeCheck_join cg 1200001 3 399360 _ _ (mobiusTreeCheck_join cg 1200001 2 399360 _ _ (mobiusTreeCheck_join cg 1200001 1 399360 _ _ p198 p199) (mobiusTreeCheck_join cg 1200001 1 399488 _ _ p201 p202)) (mobiusTreeCheck_join cg 1200001 2 399616 _ _ (mobiusTreeCheck_join cg 1200001 1 399616 _ _ p205 p206) (mobiusTreeCheck_join cg 1200001 1 399744 _ _ p208 p209))) (mobiusTreeCheck_join cg 1200001 3 399872 _ _ (mobiusTreeCheck_join cg 1200001 2 399872 _ _ (mobiusTreeCheck_join cg 1200001 1 399872 _ _ p213 p214) (mobiusTreeCheck_join cg 1200001 1 400000 _ _ p216 p217)) (mobiusTreeCheck_join cg 1200001 2 400128 _ _ (mobiusTreeCheck_join cg 1200001 1 400128 _ _ p220 p221) (mobiusTreeCheck_join cg 1200001 1 400256 _ _ p223 p224)))) (mobiusTreeCheck_join cg 1200001 4 400384 _ _ (mobiusTreeCheck_join cg 1200001 3 400384 _ _ (mobiusTreeCheck_join cg 1200001 2 400384 _ _ (mobiusTreeCheck_join cg 1200001 1 400384 _ _ p229 p230) (mobiusTreeCheck_join cg 1200001 1 400512 _ _ p232 p233)) (mobiusTreeCheck_join cg 1200001 2 400640 _ _ (mobiusTreeCheck_join cg 1200001 1 400640 _ _ p236 p237) (mobiusTreeCheck_join cg 1200001 1 400768 _ _ p239 p240))) (mobiusTreeCheck_join cg 1200001 3 400896 _ _ (mobiusTreeCheck_join cg 1200001 2 400896 _ _ (mobiusTreeCheck_join cg 1200001 1 400896 _ _ p244 p245) (mobiusTreeCheck_join cg 1200001 1 401024 _ _ p247 p248)) (mobiusTreeCheck_join cg 1200001 2 401152 _ _ (mobiusTreeCheck_join cg 1200001 1 401152 _ _ p251 p252) (mobiusTreeCheck_join cg 1200001 1 401280 _ _ p254 p255))))))) (mobiusTreeCheck_join cg 1200001 7 401408 _ _ (mobiusTreeCheck_join cg 1200001 6 401408 _ _ (mobiusTreeCheck_join cg 1200001 5 401408 _ _ (mobiusTreeCheck_join cg 1200001 4 401408 _ _ (mobiusTreeCheck_join cg 1200001 3 401408 _ _ (mobiusTreeCheck_join cg 1200001 2 401408 _ _ (mobiusTreeCheck_join cg 1200001 1 401408 _ _ p263 p264) (mobiusTreeCheck_join cg 1200001 1 401536 _ _ p266 p267)) (mobiusTreeCheck_join cg 1200001 2 401664 _ _ (mobiusTreeCheck_join cg 1200001 1 401664 _ _ p270 p271) (mobiusTreeCheck_join cg 1200001 1 401792 _ _ p273 p274))) (mobiusTreeCheck_join cg 1200001 3 401920 _ _ (mobiusTreeCheck_join cg 1200001 2 401920 _ _ (mobiusTreeCheck_join cg 1200001 1 401920 _ _ p278 p279) (mobiusTreeCheck_join cg 1200001 1 402048 _ _ p281 p282)) (mobiusTreeCheck_join cg 1200001 2 402176 _ _ (mobiusTreeCheck_join cg 1200001 1 402176 _ _ p285 p286) (mobiusTreeCheck_join cg 1200001 1 402304 _ _ p288 p289)))) (mobiusTreeCheck_join cg 1200001 4 402432 _ _ (mobiusTreeCheck_join cg 1200001 3 402432 _ _ (mobiusTreeCheck_join cg 1200001 2 402432 _ _ (mobiusTreeCheck_join cg 1200001 1 402432 _ _ p294 p295) (mobiusTreeCheck_join cg 1200001 1 402560 _ _ p297 p298)) (mobiusTreeCheck_join cg 1200001 2 402688 _ _ (mobiusTreeCheck_join cg 1200001 1 402688 _ _ p301 p302) (mobiusTreeCheck_join cg 1200001 1 402816 _ _ p304 p305))) (mobiusTreeCheck_join cg 1200001 3 402944 _ _ (mobiusTreeCheck_join cg 1200001 2 402944 _ _ (mobiusTreeCheck_join cg 1200001 1 402944 _ _ p309 p310) (mobiusTreeCheck_join cg 1200001 1 403072 _ _ p312 p313)) (mobiusTreeCheck_join cg 1200001 2 403200 _ _ (mobiusTreeCheck_join cg 1200001 1 403200 _ _ p316 p317) (mobiusTreeCheck_join cg 1200001 1 403328 _ _ p319 p320))))) (mobiusTreeCheck_join cg 1200001 5 403456 _ _ (mobiusTreeCheck_join cg 1200001 4 403456 _ _ (mobiusTreeCheck_join cg 1200001 3 403456 _ _ (mobiusTreeCheck_join cg 1200001 2 403456 _ _ (mobiusTreeCheck_join cg 1200001 1 403456 _ _ p326 p327) (mobiusTreeCheck_join cg 1200001 1 403584 _ _ p329 p330)) (mobiusTreeCheck_join cg 1200001 2 403712 _ _ (mobiusTreeCheck_join cg 1200001 1 403712 _ _ p333 p334) (mobiusTreeCheck_join cg 1200001 1 403840 _ _ p336 p337))) (mobiusTreeCheck_join cg 1200001 3 403968 _ _ (mobiusTreeCheck_join cg 1200001 2 403968 _ _ (mobiusTreeCheck_join cg 1200001 1 403968 _ _ p341 p342) (mobiusTreeCheck_join cg 1200001 1 404096 _ _ p344 p345)) (mobiusTreeCheck_join cg 1200001 2 404224 _ _ (mobiusTreeCheck_join cg 1200001 1 404224 _ _ p348 p349) (mobiusTreeCheck_join cg 1200001 1 404352 _ _ p351 p352)))) (mobiusTreeCheck_join cg 1200001 4 404480 _ _ (mobiusTreeCheck_join cg 1200001 3 404480 _ _ (mobiusTreeCheck_join cg 1200001 2 404480 _ _ (mobiusTreeCheck_join cg 1200001 1 404480 _ _ p357 p358) (mobiusTreeCheck_join cg 1200001 1 404608 _ _ p360 p361)) (mobiusTreeCheck_join cg 1200001 2 404736 _ _ (mobiusTreeCheck_join cg 1200001 1 404736 _ _ p364 p365) (mobiusTreeCheck_join cg 1200001 1 404864 _ _ p367 p368))) (mobiusTreeCheck_join cg 1200001 3 404992 _ _ (mobiusTreeCheck_join cg 1200001 2 404992 _ _ (mobiusTreeCheck_join cg 1200001 1 404992 _ _ p372 p373) (mobiusTreeCheck_join cg 1200001 1 405120 _ _ p375 p376)) (mobiusTreeCheck_join cg 1200001 2 405248 _ _ (mobiusTreeCheck_join cg 1200001 1 405248 _ _ p379 p380) (mobiusTreeCheck_join cg 1200001 1 405376 _ _ p382 p383)))))) (mobiusTreeCheck_join cg 1200001 6 405504 _ _ (mobiusTreeCheck_join cg 1200001 5 405504 _ _ (mobiusTreeCheck_join cg 1200001 4 405504 _ _ (mobiusTreeCheck_join cg 1200001 3 405504 _ _ (mobiusTreeCheck_join cg 1200001 2 405504 _ _ (mobiusTreeCheck_join cg 1200001 1 405504 _ _ p390 p391) (mobiusTreeCheck_join cg 1200001 1 405632 _ _ p393 p394)) (mobiusTreeCheck_join cg 1200001 2 405760 _ _ (mobiusTreeCheck_join cg 1200001 1 405760 _ _ p397 p398) (mobiusTreeCheck_join cg 1200001 1 405888 _ _ p400 p401))) (mobiusTreeCheck_join cg 1200001 3 406016 _ _ (mobiusTreeCheck_join cg 1200001 2 406016 _ _ (mobiusTreeCheck_join cg 1200001 1 406016 _ _ p405 p406) (mobiusTreeCheck_join cg 1200001 1 406144 _ _ p408 p409)) (mobiusTreeCheck_join cg 1200001 2 406272 _ _ (mobiusTreeCheck_join cg 1200001 1 406272 _ _ p412 p413) (mobiusTreeCheck_join cg 1200001 1 406400 _ _ p415 p416)))) (mobiusTreeCheck_join cg 1200001 4 406528 _ _ (mobiusTreeCheck_join cg 1200001 3 406528 _ _ (mobiusTreeCheck_join cg 1200001 2 406528 _ _ (mobiusTreeCheck_join cg 1200001 1 406528 _ _ p421 p422) (mobiusTreeCheck_join cg 1200001 1 406656 _ _ p424 p425)) (mobiusTreeCheck_join cg 1200001 2 406784 _ _ (mobiusTreeCheck_join cg 1200001 1 406784 _ _ p428 p429) (mobiusTreeCheck_join cg 1200001 1 406912 _ _ p431 p432))) (mobiusTreeCheck_join cg 1200001 3 407040 _ _ (mobiusTreeCheck_join cg 1200001 2 407040 _ _ (mobiusTreeCheck_join cg 1200001 1 407040 _ _ p436 p437) (mobiusTreeCheck_join cg 1200001 1 407168 _ _ p439 p440)) (mobiusTreeCheck_join cg 1200001 2 407296 _ _ (mobiusTreeCheck_join cg 1200001 1 407296 _ _ p443 p444) (mobiusTreeCheck_join cg 1200001 1 407424 _ _ p446 p447))))) (mobiusTreeCheck_join cg 1200001 5 407552 _ _ (mobiusTreeCheck_join cg 1200001 4 407552 _ _ (mobiusTreeCheck_join cg 1200001 3 407552 _ _ (mobiusTreeCheck_join cg 1200001 2 407552 _ _ (mobiusTreeCheck_join cg 1200001 1 407552 _ _ p453 p454) (mobiusTreeCheck_join cg 1200001 1 407680 _ _ p456 p457)) (mobiusTreeCheck_join cg 1200001 2 407808 _ _ (mobiusTreeCheck_join cg 1200001 1 407808 _ _ p460 p461) (mobiusTreeCheck_join cg 1200001 1 407936 _ _ p463 p464))) (mobiusTreeCheck_join cg 1200001 3 408064 _ _ (mobiusTreeCheck_join cg 1200001 2 408064 _ _ (mobiusTreeCheck_join cg 1200001 1 408064 _ _ p468 p469) (mobiusTreeCheck_join cg 1200001 1 408192 _ _ p471 p472)) (mobiusTreeCheck_join cg 1200001 2 408320 _ _ (mobiusTreeCheck_join cg 1200001 1 408320 _ _ p475 p476) (mobiusTreeCheck_join cg 1200001 1 408448 _ _ p478 p479)))) (mobiusTreeCheck_join cg 1200001 4 408576 _ _ (mobiusTreeCheck_join cg 1200001 3 408576 _ _ (mobiusTreeCheck_join cg 1200001 2 408576 _ _ (mobiusTreeCheck_join cg 1200001 1 408576 _ _ p484 p485) (mobiusTreeCheck_join cg 1200001 1 408704 _ _ p487 p488)) (mobiusTreeCheck_join cg 1200001 2 408832 _ _ (mobiusTreeCheck_join cg 1200001 1 408832 _ _ p491 p492) (mobiusTreeCheck_join cg 1200001 1 408960 _ _ p494 p495))) (mobiusTreeCheck_join cg 1200001 3 409088 _ _ (mobiusTreeCheck_join cg 1200001 2 409088 _ _ (mobiusTreeCheck_join cg 1200001 1 409088 _ _ p499 p500) (mobiusTreeCheck_join cg 1200001 1 409216 _ _ p502 p503)) (mobiusTreeCheck_join cg 1200001 2 409344 _ _ (mobiusTreeCheck_join cg 1200001 1 409344 _ _ p506 p507) (mobiusTreeCheck_join cg 1200001 1 409472 _ _ p509 p510))))))))

end Helfgott

open Helfgott
theorem solution : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 393216 (MobiusCertTree.branch mobiusTableBlock048 mobiusTableBlock049) = true := Helfgott.combined

#print axioms solution
