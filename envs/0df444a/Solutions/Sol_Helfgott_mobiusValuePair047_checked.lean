-- Prove2me | solution 1 for Helfgott.mobiusValuePair047_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:43:48.305604+00:00
-- url     : https://prove2.me/submissions/62229927-e993-4225-8f02-8d3866a0071e

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

private abbrev d8 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 0
private theorem p8 : mobiusTreeCheck cg 1200001 1 770048 d8 = true := by decide +kernel

private abbrev d9 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 1
private theorem p9 : mobiusTreeCheck cg 1200001 1 770112 d9 = true := by decide +kernel

private def d7 : MobiusCertTree := .branch d8 d9
private abbrev d11 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 2
private theorem p11 : mobiusTreeCheck cg 1200001 1 770176 d11 = true := by decide +kernel

private abbrev d12 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 3
private theorem p12 : mobiusTreeCheck cg 1200001 1 770240 d12 = true := by decide +kernel

private def d10 : MobiusCertTree := .branch d11 d12
private def d6 : MobiusCertTree := .branch d7 d10
private abbrev d15 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 4
private theorem p15 : mobiusTreeCheck cg 1200001 1 770304 d15 = true := by decide +kernel

private abbrev d16 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 5
private theorem p16 : mobiusTreeCheck cg 1200001 1 770368 d16 = true := by decide +kernel

private def d14 : MobiusCertTree := .branch d15 d16
private abbrev d18 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 6
private theorem p18 : mobiusTreeCheck cg 1200001 1 770432 d18 = true := by decide +kernel

private abbrev d19 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 7
private theorem p19 : mobiusTreeCheck cg 1200001 1 770496 d19 = true := by decide +kernel

private def d17 : MobiusCertTree := .branch d18 d19
private def d13 : MobiusCertTree := .branch d14 d17
private def d5 : MobiusCertTree := .branch d6 d13
private abbrev d23 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 8
private theorem p23 : mobiusTreeCheck cg 1200001 1 770560 d23 = true := by decide +kernel

private abbrev d24 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 9
private theorem p24 : mobiusTreeCheck cg 1200001 1 770624 d24 = true := by decide +kernel

private def d22 : MobiusCertTree := .branch d23 d24
private abbrev d26 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 10
private theorem p26 : mobiusTreeCheck cg 1200001 1 770688 d26 = true := by decide +kernel

private abbrev d27 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 11
private theorem p27 : mobiusTreeCheck cg 1200001 1 770752 d27 = true := by decide +kernel

private def d25 : MobiusCertTree := .branch d26 d27
private def d21 : MobiusCertTree := .branch d22 d25
private abbrev d30 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 12
private theorem p30 : mobiusTreeCheck cg 1200001 1 770816 d30 = true := by decide +kernel

private abbrev d31 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 13
private theorem p31 : mobiusTreeCheck cg 1200001 1 770880 d31 = true := by decide +kernel

private def d29 : MobiusCertTree := .branch d30 d31
private abbrev d33 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 14
private theorem p33 : mobiusTreeCheck cg 1200001 1 770944 d33 = true := by decide +kernel

private abbrev d34 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 15
private theorem p34 : mobiusTreeCheck cg 1200001 1 771008 d34 = true := by decide +kernel

private def d32 : MobiusCertTree := .branch d33 d34
private def d28 : MobiusCertTree := .branch d29 d32
private def d20 : MobiusCertTree := .branch d21 d28
private def d4 : MobiusCertTree := .branch d5 d20
private abbrev d39 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 16
private theorem p39 : mobiusTreeCheck cg 1200001 1 771072 d39 = true := by decide +kernel

private abbrev d40 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 17
private theorem p40 : mobiusTreeCheck cg 1200001 1 771136 d40 = true := by decide +kernel

private def d38 : MobiusCertTree := .branch d39 d40
private abbrev d42 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 18
private theorem p42 : mobiusTreeCheck cg 1200001 1 771200 d42 = true := by decide +kernel

private abbrev d43 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 19
private theorem p43 : mobiusTreeCheck cg 1200001 1 771264 d43 = true := by decide +kernel

private def d41 : MobiusCertTree := .branch d42 d43
private def d37 : MobiusCertTree := .branch d38 d41
private abbrev d46 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 20
private theorem p46 : mobiusTreeCheck cg 1200001 1 771328 d46 = true := by decide +kernel

private abbrev d47 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 21
private theorem p47 : mobiusTreeCheck cg 1200001 1 771392 d47 = true := by decide +kernel

private def d45 : MobiusCertTree := .branch d46 d47
private abbrev d49 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 22
private theorem p49 : mobiusTreeCheck cg 1200001 1 771456 d49 = true := by decide +kernel

private abbrev d50 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 23
private theorem p50 : mobiusTreeCheck cg 1200001 1 771520 d50 = true := by decide +kernel

private def d48 : MobiusCertTree := .branch d49 d50
private def d44 : MobiusCertTree := .branch d45 d48
private def d36 : MobiusCertTree := .branch d37 d44
private abbrev d54 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 24
private theorem p54 : mobiusTreeCheck cg 1200001 1 771584 d54 = true := by decide +kernel

private abbrev d55 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 25
private theorem p55 : mobiusTreeCheck cg 1200001 1 771648 d55 = true := by decide +kernel

private def d53 : MobiusCertTree := .branch d54 d55
private abbrev d57 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 26
private theorem p57 : mobiusTreeCheck cg 1200001 1 771712 d57 = true := by decide +kernel

private abbrev d58 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 27
private theorem p58 : mobiusTreeCheck cg 1200001 1 771776 d58 = true := by decide +kernel

private def d56 : MobiusCertTree := .branch d57 d58
private def d52 : MobiusCertTree := .branch d53 d56
private abbrev d61 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 28
private theorem p61 : mobiusTreeCheck cg 1200001 1 771840 d61 = true := by decide +kernel

private abbrev d62 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 29
private theorem p62 : mobiusTreeCheck cg 1200001 1 771904 d62 = true := by decide +kernel

private def d60 : MobiusCertTree := .branch d61 d62
private abbrev d64 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 30
private theorem p64 : mobiusTreeCheck cg 1200001 1 771968 d64 = true := by decide +kernel

private abbrev d65 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 31
private theorem p65 : mobiusTreeCheck cg 1200001 1 772032 d65 = true := by decide +kernel

private def d63 : MobiusCertTree := .branch d64 d65
private def d59 : MobiusCertTree := .branch d60 d63
private def d51 : MobiusCertTree := .branch d52 d59
private def d35 : MobiusCertTree := .branch d36 d51
private def d3 : MobiusCertTree := .branch d4 d35
private abbrev d71 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 32
private theorem p71 : mobiusTreeCheck cg 1200001 1 772096 d71 = true := by decide +kernel

private abbrev d72 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 33
private theorem p72 : mobiusTreeCheck cg 1200001 1 772160 d72 = true := by decide +kernel

private def d70 : MobiusCertTree := .branch d71 d72
private abbrev d74 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 34
private theorem p74 : mobiusTreeCheck cg 1200001 1 772224 d74 = true := by decide +kernel

private abbrev d75 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 35
private theorem p75 : mobiusTreeCheck cg 1200001 1 772288 d75 = true := by decide +kernel

private def d73 : MobiusCertTree := .branch d74 d75
private def d69 : MobiusCertTree := .branch d70 d73
private abbrev d78 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 36
private theorem p78 : mobiusTreeCheck cg 1200001 1 772352 d78 = true := by decide +kernel

private abbrev d79 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 37
private theorem p79 : mobiusTreeCheck cg 1200001 1 772416 d79 = true := by decide +kernel

private def d77 : MobiusCertTree := .branch d78 d79
private abbrev d81 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 38
private theorem p81 : mobiusTreeCheck cg 1200001 1 772480 d81 = true := by decide +kernel

private abbrev d82 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 39
private theorem p82 : mobiusTreeCheck cg 1200001 1 772544 d82 = true := by decide +kernel

private def d80 : MobiusCertTree := .branch d81 d82
private def d76 : MobiusCertTree := .branch d77 d80
private def d68 : MobiusCertTree := .branch d69 d76
private abbrev d86 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 40
private theorem p86 : mobiusTreeCheck cg 1200001 1 772608 d86 = true := by decide +kernel

private abbrev d87 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 41
private theorem p87 : mobiusTreeCheck cg 1200001 1 772672 d87 = true := by decide +kernel

private def d85 : MobiusCertTree := .branch d86 d87
private abbrev d89 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 42
private theorem p89 : mobiusTreeCheck cg 1200001 1 772736 d89 = true := by decide +kernel

private abbrev d90 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 43
private theorem p90 : mobiusTreeCheck cg 1200001 1 772800 d90 = true := by decide +kernel

private def d88 : MobiusCertTree := .branch d89 d90
private def d84 : MobiusCertTree := .branch d85 d88
private abbrev d93 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 44
private theorem p93 : mobiusTreeCheck cg 1200001 1 772864 d93 = true := by decide +kernel

private abbrev d94 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 45
private theorem p94 : mobiusTreeCheck cg 1200001 1 772928 d94 = true := by decide +kernel

private def d92 : MobiusCertTree := .branch d93 d94
private abbrev d96 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 46
private theorem p96 : mobiusTreeCheck cg 1200001 1 772992 d96 = true := by decide +kernel

private abbrev d97 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 47
private theorem p97 : mobiusTreeCheck cg 1200001 1 773056 d97 = true := by decide +kernel

private def d95 : MobiusCertTree := .branch d96 d97
private def d91 : MobiusCertTree := .branch d92 d95
private def d83 : MobiusCertTree := .branch d84 d91
private def d67 : MobiusCertTree := .branch d68 d83
private abbrev d102 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 48
private theorem p102 : mobiusTreeCheck cg 1200001 1 773120 d102 = true := by decide +kernel

private abbrev d103 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 49
private theorem p103 : mobiusTreeCheck cg 1200001 1 773184 d103 = true := by decide +kernel

private def d101 : MobiusCertTree := .branch d102 d103
private abbrev d105 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 50
private theorem p105 : mobiusTreeCheck cg 1200001 1 773248 d105 = true := by decide +kernel

private abbrev d106 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 51
private theorem p106 : mobiusTreeCheck cg 1200001 1 773312 d106 = true := by decide +kernel

private def d104 : MobiusCertTree := .branch d105 d106
private def d100 : MobiusCertTree := .branch d101 d104
private abbrev d109 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 52
private theorem p109 : mobiusTreeCheck cg 1200001 1 773376 d109 = true := by decide +kernel

private abbrev d110 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 53
private theorem p110 : mobiusTreeCheck cg 1200001 1 773440 d110 = true := by decide +kernel

private def d108 : MobiusCertTree := .branch d109 d110
private abbrev d112 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 54
private theorem p112 : mobiusTreeCheck cg 1200001 1 773504 d112 = true := by decide +kernel

private abbrev d113 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 55
private theorem p113 : mobiusTreeCheck cg 1200001 1 773568 d113 = true := by decide +kernel

private def d111 : MobiusCertTree := .branch d112 d113
private def d107 : MobiusCertTree := .branch d108 d111
private def d99 : MobiusCertTree := .branch d100 d107
private abbrev d117 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 56
private theorem p117 : mobiusTreeCheck cg 1200001 1 773632 d117 = true := by decide +kernel

private abbrev d118 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 57
private theorem p118 : mobiusTreeCheck cg 1200001 1 773696 d118 = true := by decide +kernel

private def d116 : MobiusCertTree := .branch d117 d118
private abbrev d120 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 58
private theorem p120 : mobiusTreeCheck cg 1200001 1 773760 d120 = true := by decide +kernel

private abbrev d121 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 59
private theorem p121 : mobiusTreeCheck cg 1200001 1 773824 d121 = true := by decide +kernel

private def d119 : MobiusCertTree := .branch d120 d121
private def d115 : MobiusCertTree := .branch d116 d119
private abbrev d124 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 60
private theorem p124 : mobiusTreeCheck cg 1200001 1 773888 d124 = true := by decide +kernel

private abbrev d125 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 61
private theorem p125 : mobiusTreeCheck cg 1200001 1 773952 d125 = true := by decide +kernel

private def d123 : MobiusCertTree := .branch d124 d125
private abbrev d127 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 62
private theorem p127 : mobiusTreeCheck cg 1200001 1 774016 d127 = true := by decide +kernel

private abbrev d128 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 63
private theorem p128 : mobiusTreeCheck cg 1200001 1 774080 d128 = true := by decide +kernel

private def d126 : MobiusCertTree := .branch d127 d128
private def d122 : MobiusCertTree := .branch d123 d126
private def d114 : MobiusCertTree := .branch d115 d122
private def d98 : MobiusCertTree := .branch d99 d114
private def d66 : MobiusCertTree := .branch d67 d98
private def d2 : MobiusCertTree := .branch d3 d66
private abbrev d135 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 64
private theorem p135 : mobiusTreeCheck cg 1200001 1 774144 d135 = true := by decide +kernel

private abbrev d136 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 65
private theorem p136 : mobiusTreeCheck cg 1200001 1 774208 d136 = true := by decide +kernel

private def d134 : MobiusCertTree := .branch d135 d136
private abbrev d138 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 66
private theorem p138 : mobiusTreeCheck cg 1200001 1 774272 d138 = true := by decide +kernel

private abbrev d139 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 67
private theorem p139 : mobiusTreeCheck cg 1200001 1 774336 d139 = true := by decide +kernel

private def d137 : MobiusCertTree := .branch d138 d139
private def d133 : MobiusCertTree := .branch d134 d137
private abbrev d142 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 68
private theorem p142 : mobiusTreeCheck cg 1200001 1 774400 d142 = true := by decide +kernel

private abbrev d143 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 69
private theorem p143 : mobiusTreeCheck cg 1200001 1 774464 d143 = true := by decide +kernel

private def d141 : MobiusCertTree := .branch d142 d143
private abbrev d145 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 70
private theorem p145 : mobiusTreeCheck cg 1200001 1 774528 d145 = true := by decide +kernel

private abbrev d146 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 71
private theorem p146 : mobiusTreeCheck cg 1200001 1 774592 d146 = true := by decide +kernel

private def d144 : MobiusCertTree := .branch d145 d146
private def d140 : MobiusCertTree := .branch d141 d144
private def d132 : MobiusCertTree := .branch d133 d140
private abbrev d150 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 72
private theorem p150 : mobiusTreeCheck cg 1200001 1 774656 d150 = true := by decide +kernel

private abbrev d151 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 73
private theorem p151 : mobiusTreeCheck cg 1200001 1 774720 d151 = true := by decide +kernel

private def d149 : MobiusCertTree := .branch d150 d151
private abbrev d153 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 74
private theorem p153 : mobiusTreeCheck cg 1200001 1 774784 d153 = true := by decide +kernel

private abbrev d154 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 75
private theorem p154 : mobiusTreeCheck cg 1200001 1 774848 d154 = true := by decide +kernel

private def d152 : MobiusCertTree := .branch d153 d154
private def d148 : MobiusCertTree := .branch d149 d152
private abbrev d157 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 76
private theorem p157 : mobiusTreeCheck cg 1200001 1 774912 d157 = true := by decide +kernel

private abbrev d158 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 77
private theorem p158 : mobiusTreeCheck cg 1200001 1 774976 d158 = true := by decide +kernel

private def d156 : MobiusCertTree := .branch d157 d158
private abbrev d160 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 78
private theorem p160 : mobiusTreeCheck cg 1200001 1 775040 d160 = true := by decide +kernel

private abbrev d161 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 79
private theorem p161 : mobiusTreeCheck cg 1200001 1 775104 d161 = true := by decide +kernel

private def d159 : MobiusCertTree := .branch d160 d161
private def d155 : MobiusCertTree := .branch d156 d159
private def d147 : MobiusCertTree := .branch d148 d155
private def d131 : MobiusCertTree := .branch d132 d147
private abbrev d166 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 80
private theorem p166 : mobiusTreeCheck cg 1200001 1 775168 d166 = true := by decide +kernel

private abbrev d167 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 81
private theorem p167 : mobiusTreeCheck cg 1200001 1 775232 d167 = true := by decide +kernel

private def d165 : MobiusCertTree := .branch d166 d167
private abbrev d169 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 82
private theorem p169 : mobiusTreeCheck cg 1200001 1 775296 d169 = true := by decide +kernel

private abbrev d170 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 83
private theorem p170 : mobiusTreeCheck cg 1200001 1 775360 d170 = true := by decide +kernel

private def d168 : MobiusCertTree := .branch d169 d170
private def d164 : MobiusCertTree := .branch d165 d168
private abbrev d173 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 84
private theorem p173 : mobiusTreeCheck cg 1200001 1 775424 d173 = true := by decide +kernel

private abbrev d174 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 85
private theorem p174 : mobiusTreeCheck cg 1200001 1 775488 d174 = true := by decide +kernel

private def d172 : MobiusCertTree := .branch d173 d174
private abbrev d176 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 86
private theorem p176 : mobiusTreeCheck cg 1200001 1 775552 d176 = true := by decide +kernel

private abbrev d177 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 87
private theorem p177 : mobiusTreeCheck cg 1200001 1 775616 d177 = true := by decide +kernel

private def d175 : MobiusCertTree := .branch d176 d177
private def d171 : MobiusCertTree := .branch d172 d175
private def d163 : MobiusCertTree := .branch d164 d171
private abbrev d181 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 88
private theorem p181 : mobiusTreeCheck cg 1200001 1 775680 d181 = true := by decide +kernel

private abbrev d182 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 89
private theorem p182 : mobiusTreeCheck cg 1200001 1 775744 d182 = true := by decide +kernel

private def d180 : MobiusCertTree := .branch d181 d182
private abbrev d184 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 90
private theorem p184 : mobiusTreeCheck cg 1200001 1 775808 d184 = true := by decide +kernel

private abbrev d185 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 91
private theorem p185 : mobiusTreeCheck cg 1200001 1 775872 d185 = true := by decide +kernel

private def d183 : MobiusCertTree := .branch d184 d185
private def d179 : MobiusCertTree := .branch d180 d183
private abbrev d188 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 92
private theorem p188 : mobiusTreeCheck cg 1200001 1 775936 d188 = true := by decide +kernel

private abbrev d189 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 93
private theorem p189 : mobiusTreeCheck cg 1200001 1 776000 d189 = true := by decide +kernel

private def d187 : MobiusCertTree := .branch d188 d189
private abbrev d191 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 94
private theorem p191 : mobiusTreeCheck cg 1200001 1 776064 d191 = true := by decide +kernel

private abbrev d192 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 95
private theorem p192 : mobiusTreeCheck cg 1200001 1 776128 d192 = true := by decide +kernel

private def d190 : MobiusCertTree := .branch d191 d192
private def d186 : MobiusCertTree := .branch d187 d190
private def d178 : MobiusCertTree := .branch d179 d186
private def d162 : MobiusCertTree := .branch d163 d178
private def d130 : MobiusCertTree := .branch d131 d162
private abbrev d198 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 96
private theorem p198 : mobiusTreeCheck cg 1200001 1 776192 d198 = true := by decide +kernel

private abbrev d199 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 97
private theorem p199 : mobiusTreeCheck cg 1200001 1 776256 d199 = true := by decide +kernel

private def d197 : MobiusCertTree := .branch d198 d199
private abbrev d201 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 98
private theorem p201 : mobiusTreeCheck cg 1200001 1 776320 d201 = true := by decide +kernel

private abbrev d202 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 99
private theorem p202 : mobiusTreeCheck cg 1200001 1 776384 d202 = true := by decide +kernel

private def d200 : MobiusCertTree := .branch d201 d202
private def d196 : MobiusCertTree := .branch d197 d200
private abbrev d205 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 100
private theorem p205 : mobiusTreeCheck cg 1200001 1 776448 d205 = true := by decide +kernel

private abbrev d206 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 101
private theorem p206 : mobiusTreeCheck cg 1200001 1 776512 d206 = true := by decide +kernel

private def d204 : MobiusCertTree := .branch d205 d206
private abbrev d208 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 102
private theorem p208 : mobiusTreeCheck cg 1200001 1 776576 d208 = true := by decide +kernel

private abbrev d209 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 103
private theorem p209 : mobiusTreeCheck cg 1200001 1 776640 d209 = true := by decide +kernel

private def d207 : MobiusCertTree := .branch d208 d209
private def d203 : MobiusCertTree := .branch d204 d207
private def d195 : MobiusCertTree := .branch d196 d203
private abbrev d213 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 104
private theorem p213 : mobiusTreeCheck cg 1200001 1 776704 d213 = true := by decide +kernel

private abbrev d214 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 105
private theorem p214 : mobiusTreeCheck cg 1200001 1 776768 d214 = true := by decide +kernel

private def d212 : MobiusCertTree := .branch d213 d214
private abbrev d216 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 106
private theorem p216 : mobiusTreeCheck cg 1200001 1 776832 d216 = true := by decide +kernel

private abbrev d217 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 107
private theorem p217 : mobiusTreeCheck cg 1200001 1 776896 d217 = true := by decide +kernel

private def d215 : MobiusCertTree := .branch d216 d217
private def d211 : MobiusCertTree := .branch d212 d215
private abbrev d220 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 108
private theorem p220 : mobiusTreeCheck cg 1200001 1 776960 d220 = true := by decide +kernel

private abbrev d221 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 109
private theorem p221 : mobiusTreeCheck cg 1200001 1 777024 d221 = true := by decide +kernel

private def d219 : MobiusCertTree := .branch d220 d221
private abbrev d223 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 110
private theorem p223 : mobiusTreeCheck cg 1200001 1 777088 d223 = true := by decide +kernel

private abbrev d224 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 111
private theorem p224 : mobiusTreeCheck cg 1200001 1 777152 d224 = true := by decide +kernel

private def d222 : MobiusCertTree := .branch d223 d224
private def d218 : MobiusCertTree := .branch d219 d222
private def d210 : MobiusCertTree := .branch d211 d218
private def d194 : MobiusCertTree := .branch d195 d210
private abbrev d229 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 112
private theorem p229 : mobiusTreeCheck cg 1200001 1 777216 d229 = true := by decide +kernel

private abbrev d230 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 113
private theorem p230 : mobiusTreeCheck cg 1200001 1 777280 d230 = true := by decide +kernel

private def d228 : MobiusCertTree := .branch d229 d230
private abbrev d232 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 114
private theorem p232 : mobiusTreeCheck cg 1200001 1 777344 d232 = true := by decide +kernel

private abbrev d233 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 115
private theorem p233 : mobiusTreeCheck cg 1200001 1 777408 d233 = true := by decide +kernel

private def d231 : MobiusCertTree := .branch d232 d233
private def d227 : MobiusCertTree := .branch d228 d231
private abbrev d236 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 116
private theorem p236 : mobiusTreeCheck cg 1200001 1 777472 d236 = true := by decide +kernel

private abbrev d237 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 117
private theorem p237 : mobiusTreeCheck cg 1200001 1 777536 d237 = true := by decide +kernel

private def d235 : MobiusCertTree := .branch d236 d237
private abbrev d239 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 118
private theorem p239 : mobiusTreeCheck cg 1200001 1 777600 d239 = true := by decide +kernel

private abbrev d240 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 119
private theorem p240 : mobiusTreeCheck cg 1200001 1 777664 d240 = true := by decide +kernel

private def d238 : MobiusCertTree := .branch d239 d240
private def d234 : MobiusCertTree := .branch d235 d238
private def d226 : MobiusCertTree := .branch d227 d234
private abbrev d244 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 120
private theorem p244 : mobiusTreeCheck cg 1200001 1 777728 d244 = true := by decide +kernel

private abbrev d245 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 121
private theorem p245 : mobiusTreeCheck cg 1200001 1 777792 d245 = true := by decide +kernel

private def d243 : MobiusCertTree := .branch d244 d245
private abbrev d247 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 122
private theorem p247 : mobiusTreeCheck cg 1200001 1 777856 d247 = true := by decide +kernel

private abbrev d248 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 123
private theorem p248 : mobiusTreeCheck cg 1200001 1 777920 d248 = true := by decide +kernel

private def d246 : MobiusCertTree := .branch d247 d248
private def d242 : MobiusCertTree := .branch d243 d246
private abbrev d251 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 124
private theorem p251 : mobiusTreeCheck cg 1200001 1 777984 d251 = true := by decide +kernel

private abbrev d252 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 125
private theorem p252 : mobiusTreeCheck cg 1200001 1 778048 d252 = true := by decide +kernel

private def d250 : MobiusCertTree := .branch d251 d252
private abbrev d254 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 126
private theorem p254 : mobiusTreeCheck cg 1200001 1 778112 d254 = true := by decide +kernel

private abbrev d255 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock094 127
private theorem p255 : mobiusTreeCheck cg 1200001 1 778176 d255 = true := by decide +kernel

private def d253 : MobiusCertTree := .branch d254 d255
private def d249 : MobiusCertTree := .branch d250 d253
private def d241 : MobiusCertTree := .branch d242 d249
private def d225 : MobiusCertTree := .branch d226 d241
private def d193 : MobiusCertTree := .branch d194 d225
private def d129 : MobiusCertTree := .branch d130 d193
private def d1 : MobiusCertTree := .branch d2 d129
private abbrev d263 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 0
private theorem p263 : mobiusTreeCheck cg 1200001 1 778240 d263 = true := by decide +kernel

private abbrev d264 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 1
private theorem p264 : mobiusTreeCheck cg 1200001 1 778304 d264 = true := by decide +kernel

private def d262 : MobiusCertTree := .branch d263 d264
private abbrev d266 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 2
private theorem p266 : mobiusTreeCheck cg 1200001 1 778368 d266 = true := by decide +kernel

private abbrev d267 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 3
private theorem p267 : mobiusTreeCheck cg 1200001 1 778432 d267 = true := by decide +kernel

private def d265 : MobiusCertTree := .branch d266 d267
private def d261 : MobiusCertTree := .branch d262 d265
private abbrev d270 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 4
private theorem p270 : mobiusTreeCheck cg 1200001 1 778496 d270 = true := by decide +kernel

private abbrev d271 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 5
private theorem p271 : mobiusTreeCheck cg 1200001 1 778560 d271 = true := by decide +kernel

private def d269 : MobiusCertTree := .branch d270 d271
private abbrev d273 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 6
private theorem p273 : mobiusTreeCheck cg 1200001 1 778624 d273 = true := by decide +kernel

private abbrev d274 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 7
private theorem p274 : mobiusTreeCheck cg 1200001 1 778688 d274 = true := by decide +kernel

private def d272 : MobiusCertTree := .branch d273 d274
private def d268 : MobiusCertTree := .branch d269 d272
private def d260 : MobiusCertTree := .branch d261 d268
private abbrev d278 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 8
private theorem p278 : mobiusTreeCheck cg 1200001 1 778752 d278 = true := by decide +kernel

private abbrev d279 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 9
private theorem p279 : mobiusTreeCheck cg 1200001 1 778816 d279 = true := by decide +kernel

private def d277 : MobiusCertTree := .branch d278 d279
private abbrev d281 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 10
private theorem p281 : mobiusTreeCheck cg 1200001 1 778880 d281 = true := by decide +kernel

private abbrev d282 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 11
private theorem p282 : mobiusTreeCheck cg 1200001 1 778944 d282 = true := by decide +kernel

private def d280 : MobiusCertTree := .branch d281 d282
private def d276 : MobiusCertTree := .branch d277 d280
private abbrev d285 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 12
private theorem p285 : mobiusTreeCheck cg 1200001 1 779008 d285 = true := by decide +kernel

private abbrev d286 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 13
private theorem p286 : mobiusTreeCheck cg 1200001 1 779072 d286 = true := by decide +kernel

private def d284 : MobiusCertTree := .branch d285 d286
private abbrev d288 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 14
private theorem p288 : mobiusTreeCheck cg 1200001 1 779136 d288 = true := by decide +kernel

private abbrev d289 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 15
private theorem p289 : mobiusTreeCheck cg 1200001 1 779200 d289 = true := by decide +kernel

private def d287 : MobiusCertTree := .branch d288 d289
private def d283 : MobiusCertTree := .branch d284 d287
private def d275 : MobiusCertTree := .branch d276 d283
private def d259 : MobiusCertTree := .branch d260 d275
private abbrev d294 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 16
private theorem p294 : mobiusTreeCheck cg 1200001 1 779264 d294 = true := by decide +kernel

private abbrev d295 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 17
private theorem p295 : mobiusTreeCheck cg 1200001 1 779328 d295 = true := by decide +kernel

private def d293 : MobiusCertTree := .branch d294 d295
private abbrev d297 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 18
private theorem p297 : mobiusTreeCheck cg 1200001 1 779392 d297 = true := by decide +kernel

private abbrev d298 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 19
private theorem p298 : mobiusTreeCheck cg 1200001 1 779456 d298 = true := by decide +kernel

private def d296 : MobiusCertTree := .branch d297 d298
private def d292 : MobiusCertTree := .branch d293 d296
private abbrev d301 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 20
private theorem p301 : mobiusTreeCheck cg 1200001 1 779520 d301 = true := by decide +kernel

private abbrev d302 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 21
private theorem p302 : mobiusTreeCheck cg 1200001 1 779584 d302 = true := by decide +kernel

private def d300 : MobiusCertTree := .branch d301 d302
private abbrev d304 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 22
private theorem p304 : mobiusTreeCheck cg 1200001 1 779648 d304 = true := by decide +kernel

private abbrev d305 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 23
private theorem p305 : mobiusTreeCheck cg 1200001 1 779712 d305 = true := by decide +kernel

private def d303 : MobiusCertTree := .branch d304 d305
private def d299 : MobiusCertTree := .branch d300 d303
private def d291 : MobiusCertTree := .branch d292 d299
private abbrev d309 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 24
private theorem p309 : mobiusTreeCheck cg 1200001 1 779776 d309 = true := by decide +kernel

private abbrev d310 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 25
private theorem p310 : mobiusTreeCheck cg 1200001 1 779840 d310 = true := by decide +kernel

private def d308 : MobiusCertTree := .branch d309 d310
private abbrev d312 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 26
private theorem p312 : mobiusTreeCheck cg 1200001 1 779904 d312 = true := by decide +kernel

private abbrev d313 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 27
private theorem p313 : mobiusTreeCheck cg 1200001 1 779968 d313 = true := by decide +kernel

private def d311 : MobiusCertTree := .branch d312 d313
private def d307 : MobiusCertTree := .branch d308 d311
private abbrev d316 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 28
private theorem p316 : mobiusTreeCheck cg 1200001 1 780032 d316 = true := by decide +kernel

private abbrev d317 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 29
private theorem p317 : mobiusTreeCheck cg 1200001 1 780096 d317 = true := by decide +kernel

private def d315 : MobiusCertTree := .branch d316 d317
private abbrev d319 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 30
private theorem p319 : mobiusTreeCheck cg 1200001 1 780160 d319 = true := by decide +kernel

private abbrev d320 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 31
private theorem p320 : mobiusTreeCheck cg 1200001 1 780224 d320 = true := by decide +kernel

private def d318 : MobiusCertTree := .branch d319 d320
private def d314 : MobiusCertTree := .branch d315 d318
private def d306 : MobiusCertTree := .branch d307 d314
private def d290 : MobiusCertTree := .branch d291 d306
private def d258 : MobiusCertTree := .branch d259 d290
private abbrev d326 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 32
private theorem p326 : mobiusTreeCheck cg 1200001 1 780288 d326 = true := by decide +kernel

private abbrev d327 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 33
private theorem p327 : mobiusTreeCheck cg 1200001 1 780352 d327 = true := by decide +kernel

private def d325 : MobiusCertTree := .branch d326 d327
private abbrev d329 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 34
private theorem p329 : mobiusTreeCheck cg 1200001 1 780416 d329 = true := by decide +kernel

private abbrev d330 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 35
private theorem p330 : mobiusTreeCheck cg 1200001 1 780480 d330 = true := by decide +kernel

private def d328 : MobiusCertTree := .branch d329 d330
private def d324 : MobiusCertTree := .branch d325 d328
private abbrev d333 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 36
private theorem p333 : mobiusTreeCheck cg 1200001 1 780544 d333 = true := by decide +kernel

private abbrev d334 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 37
private theorem p334 : mobiusTreeCheck cg 1200001 1 780608 d334 = true := by decide +kernel

private def d332 : MobiusCertTree := .branch d333 d334
private abbrev d336 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 38
private theorem p336 : mobiusTreeCheck cg 1200001 1 780672 d336 = true := by decide +kernel

private abbrev d337 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 39
private theorem p337 : mobiusTreeCheck cg 1200001 1 780736 d337 = true := by decide +kernel

private def d335 : MobiusCertTree := .branch d336 d337
private def d331 : MobiusCertTree := .branch d332 d335
private def d323 : MobiusCertTree := .branch d324 d331
private abbrev d341 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 40
private theorem p341 : mobiusTreeCheck cg 1200001 1 780800 d341 = true := by decide +kernel

private abbrev d342 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 41
private theorem p342 : mobiusTreeCheck cg 1200001 1 780864 d342 = true := by decide +kernel

private def d340 : MobiusCertTree := .branch d341 d342
private abbrev d344 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 42
private theorem p344 : mobiusTreeCheck cg 1200001 1 780928 d344 = true := by decide +kernel

private abbrev d345 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 43
private theorem p345 : mobiusTreeCheck cg 1200001 1 780992 d345 = true := by decide +kernel

private def d343 : MobiusCertTree := .branch d344 d345
private def d339 : MobiusCertTree := .branch d340 d343
private abbrev d348 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 44
private theorem p348 : mobiusTreeCheck cg 1200001 1 781056 d348 = true := by decide +kernel

private abbrev d349 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 45
private theorem p349 : mobiusTreeCheck cg 1200001 1 781120 d349 = true := by decide +kernel

private def d347 : MobiusCertTree := .branch d348 d349
private abbrev d351 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 46
private theorem p351 : mobiusTreeCheck cg 1200001 1 781184 d351 = true := by decide +kernel

private abbrev d352 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 47
private theorem p352 : mobiusTreeCheck cg 1200001 1 781248 d352 = true := by decide +kernel

private def d350 : MobiusCertTree := .branch d351 d352
private def d346 : MobiusCertTree := .branch d347 d350
private def d338 : MobiusCertTree := .branch d339 d346
private def d322 : MobiusCertTree := .branch d323 d338
private abbrev d357 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 48
private theorem p357 : mobiusTreeCheck cg 1200001 1 781312 d357 = true := by decide +kernel

private abbrev d358 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 49
private theorem p358 : mobiusTreeCheck cg 1200001 1 781376 d358 = true := by decide +kernel

private def d356 : MobiusCertTree := .branch d357 d358
private abbrev d360 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 50
private theorem p360 : mobiusTreeCheck cg 1200001 1 781440 d360 = true := by decide +kernel

private abbrev d361 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 51
private theorem p361 : mobiusTreeCheck cg 1200001 1 781504 d361 = true := by decide +kernel

private def d359 : MobiusCertTree := .branch d360 d361
private def d355 : MobiusCertTree := .branch d356 d359
private abbrev d364 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 52
private theorem p364 : mobiusTreeCheck cg 1200001 1 781568 d364 = true := by decide +kernel

private abbrev d365 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 53
private theorem p365 : mobiusTreeCheck cg 1200001 1 781632 d365 = true := by decide +kernel

private def d363 : MobiusCertTree := .branch d364 d365
private abbrev d367 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 54
private theorem p367 : mobiusTreeCheck cg 1200001 1 781696 d367 = true := by decide +kernel

private abbrev d368 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 55
private theorem p368 : mobiusTreeCheck cg 1200001 1 781760 d368 = true := by decide +kernel

private def d366 : MobiusCertTree := .branch d367 d368
private def d362 : MobiusCertTree := .branch d363 d366
private def d354 : MobiusCertTree := .branch d355 d362
private abbrev d372 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 56
private theorem p372 : mobiusTreeCheck cg 1200001 1 781824 d372 = true := by decide +kernel

private abbrev d373 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 57
private theorem p373 : mobiusTreeCheck cg 1200001 1 781888 d373 = true := by decide +kernel

private def d371 : MobiusCertTree := .branch d372 d373
private abbrev d375 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 58
private theorem p375 : mobiusTreeCheck cg 1200001 1 781952 d375 = true := by decide +kernel

private abbrev d376 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 59
private theorem p376 : mobiusTreeCheck cg 1200001 1 782016 d376 = true := by decide +kernel

private def d374 : MobiusCertTree := .branch d375 d376
private def d370 : MobiusCertTree := .branch d371 d374
private abbrev d379 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 60
private theorem p379 : mobiusTreeCheck cg 1200001 1 782080 d379 = true := by decide +kernel

private abbrev d380 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 61
private theorem p380 : mobiusTreeCheck cg 1200001 1 782144 d380 = true := by decide +kernel

private def d378 : MobiusCertTree := .branch d379 d380
private abbrev d382 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 62
private theorem p382 : mobiusTreeCheck cg 1200001 1 782208 d382 = true := by decide +kernel

private abbrev d383 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 63
private theorem p383 : mobiusTreeCheck cg 1200001 1 782272 d383 = true := by decide +kernel

private def d381 : MobiusCertTree := .branch d382 d383
private def d377 : MobiusCertTree := .branch d378 d381
private def d369 : MobiusCertTree := .branch d370 d377
private def d353 : MobiusCertTree := .branch d354 d369
private def d321 : MobiusCertTree := .branch d322 d353
private def d257 : MobiusCertTree := .branch d258 d321
private abbrev d390 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 64
private theorem p390 : mobiusTreeCheck cg 1200001 1 782336 d390 = true := by decide +kernel

private abbrev d391 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 65
private theorem p391 : mobiusTreeCheck cg 1200001 1 782400 d391 = true := by decide +kernel

private def d389 : MobiusCertTree := .branch d390 d391
private abbrev d393 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 66
private theorem p393 : mobiusTreeCheck cg 1200001 1 782464 d393 = true := by decide +kernel

private abbrev d394 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 67
private theorem p394 : mobiusTreeCheck cg 1200001 1 782528 d394 = true := by decide +kernel

private def d392 : MobiusCertTree := .branch d393 d394
private def d388 : MobiusCertTree := .branch d389 d392
private abbrev d397 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 68
private theorem p397 : mobiusTreeCheck cg 1200001 1 782592 d397 = true := by decide +kernel

private abbrev d398 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 69
private theorem p398 : mobiusTreeCheck cg 1200001 1 782656 d398 = true := by decide +kernel

private def d396 : MobiusCertTree := .branch d397 d398
private abbrev d400 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 70
private theorem p400 : mobiusTreeCheck cg 1200001 1 782720 d400 = true := by decide +kernel

private abbrev d401 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 71
private theorem p401 : mobiusTreeCheck cg 1200001 1 782784 d401 = true := by decide +kernel

private def d399 : MobiusCertTree := .branch d400 d401
private def d395 : MobiusCertTree := .branch d396 d399
private def d387 : MobiusCertTree := .branch d388 d395
private abbrev d405 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 72
private theorem p405 : mobiusTreeCheck cg 1200001 1 782848 d405 = true := by decide +kernel

private abbrev d406 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 73
private theorem p406 : mobiusTreeCheck cg 1200001 1 782912 d406 = true := by decide +kernel

private def d404 : MobiusCertTree := .branch d405 d406
private abbrev d408 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 74
private theorem p408 : mobiusTreeCheck cg 1200001 1 782976 d408 = true := by decide +kernel

private abbrev d409 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 75
private theorem p409 : mobiusTreeCheck cg 1200001 1 783040 d409 = true := by decide +kernel

private def d407 : MobiusCertTree := .branch d408 d409
private def d403 : MobiusCertTree := .branch d404 d407
private abbrev d412 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 76
private theorem p412 : mobiusTreeCheck cg 1200001 1 783104 d412 = true := by decide +kernel

private abbrev d413 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 77
private theorem p413 : mobiusTreeCheck cg 1200001 1 783168 d413 = true := by decide +kernel

private def d411 : MobiusCertTree := .branch d412 d413
private abbrev d415 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 78
private theorem p415 : mobiusTreeCheck cg 1200001 1 783232 d415 = true := by decide +kernel

private abbrev d416 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 79
private theorem p416 : mobiusTreeCheck cg 1200001 1 783296 d416 = true := by decide +kernel

private def d414 : MobiusCertTree := .branch d415 d416
private def d410 : MobiusCertTree := .branch d411 d414
private def d402 : MobiusCertTree := .branch d403 d410
private def d386 : MobiusCertTree := .branch d387 d402
private abbrev d421 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 80
private theorem p421 : mobiusTreeCheck cg 1200001 1 783360 d421 = true := by decide +kernel

private abbrev d422 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 81
private theorem p422 : mobiusTreeCheck cg 1200001 1 783424 d422 = true := by decide +kernel

private def d420 : MobiusCertTree := .branch d421 d422
private abbrev d424 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 82
private theorem p424 : mobiusTreeCheck cg 1200001 1 783488 d424 = true := by decide +kernel

private abbrev d425 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 83
private theorem p425 : mobiusTreeCheck cg 1200001 1 783552 d425 = true := by decide +kernel

private def d423 : MobiusCertTree := .branch d424 d425
private def d419 : MobiusCertTree := .branch d420 d423
private abbrev d428 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 84
private theorem p428 : mobiusTreeCheck cg 1200001 1 783616 d428 = true := by decide +kernel

private abbrev d429 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 85
private theorem p429 : mobiusTreeCheck cg 1200001 1 783680 d429 = true := by decide +kernel

private def d427 : MobiusCertTree := .branch d428 d429
private abbrev d431 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 86
private theorem p431 : mobiusTreeCheck cg 1200001 1 783744 d431 = true := by decide +kernel

private abbrev d432 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 87
private theorem p432 : mobiusTreeCheck cg 1200001 1 783808 d432 = true := by decide +kernel

private def d430 : MobiusCertTree := .branch d431 d432
private def d426 : MobiusCertTree := .branch d427 d430
private def d418 : MobiusCertTree := .branch d419 d426
private abbrev d436 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 88
private theorem p436 : mobiusTreeCheck cg 1200001 1 783872 d436 = true := by decide +kernel

private abbrev d437 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 89
private theorem p437 : mobiusTreeCheck cg 1200001 1 783936 d437 = true := by decide +kernel

private def d435 : MobiusCertTree := .branch d436 d437
private abbrev d439 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 90
private theorem p439 : mobiusTreeCheck cg 1200001 1 784000 d439 = true := by decide +kernel

private abbrev d440 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 91
private theorem p440 : mobiusTreeCheck cg 1200001 1 784064 d440 = true := by decide +kernel

private def d438 : MobiusCertTree := .branch d439 d440
private def d434 : MobiusCertTree := .branch d435 d438
private abbrev d443 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 92
private theorem p443 : mobiusTreeCheck cg 1200001 1 784128 d443 = true := by decide +kernel

private abbrev d444 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 93
private theorem p444 : mobiusTreeCheck cg 1200001 1 784192 d444 = true := by decide +kernel

private def d442 : MobiusCertTree := .branch d443 d444
private abbrev d446 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 94
private theorem p446 : mobiusTreeCheck cg 1200001 1 784256 d446 = true := by decide +kernel

private abbrev d447 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 95
private theorem p447 : mobiusTreeCheck cg 1200001 1 784320 d447 = true := by decide +kernel

private def d445 : MobiusCertTree := .branch d446 d447
private def d441 : MobiusCertTree := .branch d442 d445
private def d433 : MobiusCertTree := .branch d434 d441
private def d417 : MobiusCertTree := .branch d418 d433
private def d385 : MobiusCertTree := .branch d386 d417
private abbrev d453 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 96
private theorem p453 : mobiusTreeCheck cg 1200001 1 784384 d453 = true := by decide +kernel

private abbrev d454 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 97
private theorem p454 : mobiusTreeCheck cg 1200001 1 784448 d454 = true := by decide +kernel

private def d452 : MobiusCertTree := .branch d453 d454
private abbrev d456 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 98
private theorem p456 : mobiusTreeCheck cg 1200001 1 784512 d456 = true := by decide +kernel

private abbrev d457 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 99
private theorem p457 : mobiusTreeCheck cg 1200001 1 784576 d457 = true := by decide +kernel

private def d455 : MobiusCertTree := .branch d456 d457
private def d451 : MobiusCertTree := .branch d452 d455
private abbrev d460 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 100
private theorem p460 : mobiusTreeCheck cg 1200001 1 784640 d460 = true := by decide +kernel

private abbrev d461 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 101
private theorem p461 : mobiusTreeCheck cg 1200001 1 784704 d461 = true := by decide +kernel

private def d459 : MobiusCertTree := .branch d460 d461
private abbrev d463 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 102
private theorem p463 : mobiusTreeCheck cg 1200001 1 784768 d463 = true := by decide +kernel

private abbrev d464 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 103
private theorem p464 : mobiusTreeCheck cg 1200001 1 784832 d464 = true := by decide +kernel

private def d462 : MobiusCertTree := .branch d463 d464
private def d458 : MobiusCertTree := .branch d459 d462
private def d450 : MobiusCertTree := .branch d451 d458
private abbrev d468 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 104
private theorem p468 : mobiusTreeCheck cg 1200001 1 784896 d468 = true := by decide +kernel

private abbrev d469 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 105
private theorem p469 : mobiusTreeCheck cg 1200001 1 784960 d469 = true := by decide +kernel

private def d467 : MobiusCertTree := .branch d468 d469
private abbrev d471 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 106
private theorem p471 : mobiusTreeCheck cg 1200001 1 785024 d471 = true := by decide +kernel

private abbrev d472 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 107
private theorem p472 : mobiusTreeCheck cg 1200001 1 785088 d472 = true := by decide +kernel

private def d470 : MobiusCertTree := .branch d471 d472
private def d466 : MobiusCertTree := .branch d467 d470
private abbrev d475 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 108
private theorem p475 : mobiusTreeCheck cg 1200001 1 785152 d475 = true := by decide +kernel

private abbrev d476 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 109
private theorem p476 : mobiusTreeCheck cg 1200001 1 785216 d476 = true := by decide +kernel

private def d474 : MobiusCertTree := .branch d475 d476
private abbrev d478 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 110
private theorem p478 : mobiusTreeCheck cg 1200001 1 785280 d478 = true := by decide +kernel

private abbrev d479 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 111
private theorem p479 : mobiusTreeCheck cg 1200001 1 785344 d479 = true := by decide +kernel

private def d477 : MobiusCertTree := .branch d478 d479
private def d473 : MobiusCertTree := .branch d474 d477
private def d465 : MobiusCertTree := .branch d466 d473
private def d449 : MobiusCertTree := .branch d450 d465
private abbrev d484 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 112
private theorem p484 : mobiusTreeCheck cg 1200001 1 785408 d484 = true := by decide +kernel

private abbrev d485 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 113
private theorem p485 : mobiusTreeCheck cg 1200001 1 785472 d485 = true := by decide +kernel

private def d483 : MobiusCertTree := .branch d484 d485
private abbrev d487 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 114
private theorem p487 : mobiusTreeCheck cg 1200001 1 785536 d487 = true := by decide +kernel

private abbrev d488 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 115
private theorem p488 : mobiusTreeCheck cg 1200001 1 785600 d488 = true := by decide +kernel

private def d486 : MobiusCertTree := .branch d487 d488
private def d482 : MobiusCertTree := .branch d483 d486
private abbrev d491 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 116
private theorem p491 : mobiusTreeCheck cg 1200001 1 785664 d491 = true := by decide +kernel

private abbrev d492 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 117
private theorem p492 : mobiusTreeCheck cg 1200001 1 785728 d492 = true := by decide +kernel

private def d490 : MobiusCertTree := .branch d491 d492
private abbrev d494 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 118
private theorem p494 : mobiusTreeCheck cg 1200001 1 785792 d494 = true := by decide +kernel

private abbrev d495 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 119
private theorem p495 : mobiusTreeCheck cg 1200001 1 785856 d495 = true := by decide +kernel

private def d493 : MobiusCertTree := .branch d494 d495
private def d489 : MobiusCertTree := .branch d490 d493
private def d481 : MobiusCertTree := .branch d482 d489
private abbrev d499 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 120
private theorem p499 : mobiusTreeCheck cg 1200001 1 785920 d499 = true := by decide +kernel

private abbrev d500 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 121
private theorem p500 : mobiusTreeCheck cg 1200001 1 785984 d500 = true := by decide +kernel

private def d498 : MobiusCertTree := .branch d499 d500
private abbrev d502 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 122
private theorem p502 : mobiusTreeCheck cg 1200001 1 786048 d502 = true := by decide +kernel

private abbrev d503 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 123
private theorem p503 : mobiusTreeCheck cg 1200001 1 786112 d503 = true := by decide +kernel

private def d501 : MobiusCertTree := .branch d502 d503
private def d497 : MobiusCertTree := .branch d498 d501
private abbrev d506 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 124
private theorem p506 : mobiusTreeCheck cg 1200001 1 786176 d506 = true := by decide +kernel

private abbrev d507 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 125
private theorem p507 : mobiusTreeCheck cg 1200001 1 786240 d507 = true := by decide +kernel

private def d505 : MobiusCertTree := .branch d506 d507
private abbrev d509 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 126
private theorem p509 : mobiusTreeCheck cg 1200001 1 786304 d509 = true := by decide +kernel

private abbrev d510 : MobiusCertTree := publishedLeaf 7 mobiusTableBlock095 127
private theorem p510 : mobiusTreeCheck cg 1200001 1 786368 d510 = true := by decide +kernel

private def d508 : MobiusCertTree := .branch d509 d510
private def d504 : MobiusCertTree := .branch d505 d508
private def d496 : MobiusCertTree := .branch d497 d504
private def d480 : MobiusCertTree := .branch d481 d496
private def d448 : MobiusCertTree := .branch d449 d480
private def d384 : MobiusCertTree := .branch d385 d448
private def d256 : MobiusCertTree := .branch d257 d384
private def d0 : MobiusCertTree := .branch d1 d256

private theorem combined : mobiusTreeCheck cg 1200001 9 770048 d0 = true :=
  (mobiusTreeCheck_join cg 1200001 8 770048 _ _ (mobiusTreeCheck_join cg 1200001 7 770048 _ _ (mobiusTreeCheck_join cg 1200001 6 770048 _ _ (mobiusTreeCheck_join cg 1200001 5 770048 _ _ (mobiusTreeCheck_join cg 1200001 4 770048 _ _ (mobiusTreeCheck_join cg 1200001 3 770048 _ _ (mobiusTreeCheck_join cg 1200001 2 770048 _ _ (mobiusTreeCheck_join cg 1200001 1 770048 _ _ p8 p9) (mobiusTreeCheck_join cg 1200001 1 770176 _ _ p11 p12)) (mobiusTreeCheck_join cg 1200001 2 770304 _ _ (mobiusTreeCheck_join cg 1200001 1 770304 _ _ p15 p16) (mobiusTreeCheck_join cg 1200001 1 770432 _ _ p18 p19))) (mobiusTreeCheck_join cg 1200001 3 770560 _ _ (mobiusTreeCheck_join cg 1200001 2 770560 _ _ (mobiusTreeCheck_join cg 1200001 1 770560 _ _ p23 p24) (mobiusTreeCheck_join cg 1200001 1 770688 _ _ p26 p27)) (mobiusTreeCheck_join cg 1200001 2 770816 _ _ (mobiusTreeCheck_join cg 1200001 1 770816 _ _ p30 p31) (mobiusTreeCheck_join cg 1200001 1 770944 _ _ p33 p34)))) (mobiusTreeCheck_join cg 1200001 4 771072 _ _ (mobiusTreeCheck_join cg 1200001 3 771072 _ _ (mobiusTreeCheck_join cg 1200001 2 771072 _ _ (mobiusTreeCheck_join cg 1200001 1 771072 _ _ p39 p40) (mobiusTreeCheck_join cg 1200001 1 771200 _ _ p42 p43)) (mobiusTreeCheck_join cg 1200001 2 771328 _ _ (mobiusTreeCheck_join cg 1200001 1 771328 _ _ p46 p47) (mobiusTreeCheck_join cg 1200001 1 771456 _ _ p49 p50))) (mobiusTreeCheck_join cg 1200001 3 771584 _ _ (mobiusTreeCheck_join cg 1200001 2 771584 _ _ (mobiusTreeCheck_join cg 1200001 1 771584 _ _ p54 p55) (mobiusTreeCheck_join cg 1200001 1 771712 _ _ p57 p58)) (mobiusTreeCheck_join cg 1200001 2 771840 _ _ (mobiusTreeCheck_join cg 1200001 1 771840 _ _ p61 p62) (mobiusTreeCheck_join cg 1200001 1 771968 _ _ p64 p65))))) (mobiusTreeCheck_join cg 1200001 5 772096 _ _ (mobiusTreeCheck_join cg 1200001 4 772096 _ _ (mobiusTreeCheck_join cg 1200001 3 772096 _ _ (mobiusTreeCheck_join cg 1200001 2 772096 _ _ (mobiusTreeCheck_join cg 1200001 1 772096 _ _ p71 p72) (mobiusTreeCheck_join cg 1200001 1 772224 _ _ p74 p75)) (mobiusTreeCheck_join cg 1200001 2 772352 _ _ (mobiusTreeCheck_join cg 1200001 1 772352 _ _ p78 p79) (mobiusTreeCheck_join cg 1200001 1 772480 _ _ p81 p82))) (mobiusTreeCheck_join cg 1200001 3 772608 _ _ (mobiusTreeCheck_join cg 1200001 2 772608 _ _ (mobiusTreeCheck_join cg 1200001 1 772608 _ _ p86 p87) (mobiusTreeCheck_join cg 1200001 1 772736 _ _ p89 p90)) (mobiusTreeCheck_join cg 1200001 2 772864 _ _ (mobiusTreeCheck_join cg 1200001 1 772864 _ _ p93 p94) (mobiusTreeCheck_join cg 1200001 1 772992 _ _ p96 p97)))) (mobiusTreeCheck_join cg 1200001 4 773120 _ _ (mobiusTreeCheck_join cg 1200001 3 773120 _ _ (mobiusTreeCheck_join cg 1200001 2 773120 _ _ (mobiusTreeCheck_join cg 1200001 1 773120 _ _ p102 p103) (mobiusTreeCheck_join cg 1200001 1 773248 _ _ p105 p106)) (mobiusTreeCheck_join cg 1200001 2 773376 _ _ (mobiusTreeCheck_join cg 1200001 1 773376 _ _ p109 p110) (mobiusTreeCheck_join cg 1200001 1 773504 _ _ p112 p113))) (mobiusTreeCheck_join cg 1200001 3 773632 _ _ (mobiusTreeCheck_join cg 1200001 2 773632 _ _ (mobiusTreeCheck_join cg 1200001 1 773632 _ _ p117 p118) (mobiusTreeCheck_join cg 1200001 1 773760 _ _ p120 p121)) (mobiusTreeCheck_join cg 1200001 2 773888 _ _ (mobiusTreeCheck_join cg 1200001 1 773888 _ _ p124 p125) (mobiusTreeCheck_join cg 1200001 1 774016 _ _ p127 p128)))))) (mobiusTreeCheck_join cg 1200001 6 774144 _ _ (mobiusTreeCheck_join cg 1200001 5 774144 _ _ (mobiusTreeCheck_join cg 1200001 4 774144 _ _ (mobiusTreeCheck_join cg 1200001 3 774144 _ _ (mobiusTreeCheck_join cg 1200001 2 774144 _ _ (mobiusTreeCheck_join cg 1200001 1 774144 _ _ p135 p136) (mobiusTreeCheck_join cg 1200001 1 774272 _ _ p138 p139)) (mobiusTreeCheck_join cg 1200001 2 774400 _ _ (mobiusTreeCheck_join cg 1200001 1 774400 _ _ p142 p143) (mobiusTreeCheck_join cg 1200001 1 774528 _ _ p145 p146))) (mobiusTreeCheck_join cg 1200001 3 774656 _ _ (mobiusTreeCheck_join cg 1200001 2 774656 _ _ (mobiusTreeCheck_join cg 1200001 1 774656 _ _ p150 p151) (mobiusTreeCheck_join cg 1200001 1 774784 _ _ p153 p154)) (mobiusTreeCheck_join cg 1200001 2 774912 _ _ (mobiusTreeCheck_join cg 1200001 1 774912 _ _ p157 p158) (mobiusTreeCheck_join cg 1200001 1 775040 _ _ p160 p161)))) (mobiusTreeCheck_join cg 1200001 4 775168 _ _ (mobiusTreeCheck_join cg 1200001 3 775168 _ _ (mobiusTreeCheck_join cg 1200001 2 775168 _ _ (mobiusTreeCheck_join cg 1200001 1 775168 _ _ p166 p167) (mobiusTreeCheck_join cg 1200001 1 775296 _ _ p169 p170)) (mobiusTreeCheck_join cg 1200001 2 775424 _ _ (mobiusTreeCheck_join cg 1200001 1 775424 _ _ p173 p174) (mobiusTreeCheck_join cg 1200001 1 775552 _ _ p176 p177))) (mobiusTreeCheck_join cg 1200001 3 775680 _ _ (mobiusTreeCheck_join cg 1200001 2 775680 _ _ (mobiusTreeCheck_join cg 1200001 1 775680 _ _ p181 p182) (mobiusTreeCheck_join cg 1200001 1 775808 _ _ p184 p185)) (mobiusTreeCheck_join cg 1200001 2 775936 _ _ (mobiusTreeCheck_join cg 1200001 1 775936 _ _ p188 p189) (mobiusTreeCheck_join cg 1200001 1 776064 _ _ p191 p192))))) (mobiusTreeCheck_join cg 1200001 5 776192 _ _ (mobiusTreeCheck_join cg 1200001 4 776192 _ _ (mobiusTreeCheck_join cg 1200001 3 776192 _ _ (mobiusTreeCheck_join cg 1200001 2 776192 _ _ (mobiusTreeCheck_join cg 1200001 1 776192 _ _ p198 p199) (mobiusTreeCheck_join cg 1200001 1 776320 _ _ p201 p202)) (mobiusTreeCheck_join cg 1200001 2 776448 _ _ (mobiusTreeCheck_join cg 1200001 1 776448 _ _ p205 p206) (mobiusTreeCheck_join cg 1200001 1 776576 _ _ p208 p209))) (mobiusTreeCheck_join cg 1200001 3 776704 _ _ (mobiusTreeCheck_join cg 1200001 2 776704 _ _ (mobiusTreeCheck_join cg 1200001 1 776704 _ _ p213 p214) (mobiusTreeCheck_join cg 1200001 1 776832 _ _ p216 p217)) (mobiusTreeCheck_join cg 1200001 2 776960 _ _ (mobiusTreeCheck_join cg 1200001 1 776960 _ _ p220 p221) (mobiusTreeCheck_join cg 1200001 1 777088 _ _ p223 p224)))) (mobiusTreeCheck_join cg 1200001 4 777216 _ _ (mobiusTreeCheck_join cg 1200001 3 777216 _ _ (mobiusTreeCheck_join cg 1200001 2 777216 _ _ (mobiusTreeCheck_join cg 1200001 1 777216 _ _ p229 p230) (mobiusTreeCheck_join cg 1200001 1 777344 _ _ p232 p233)) (mobiusTreeCheck_join cg 1200001 2 777472 _ _ (mobiusTreeCheck_join cg 1200001 1 777472 _ _ p236 p237) (mobiusTreeCheck_join cg 1200001 1 777600 _ _ p239 p240))) (mobiusTreeCheck_join cg 1200001 3 777728 _ _ (mobiusTreeCheck_join cg 1200001 2 777728 _ _ (mobiusTreeCheck_join cg 1200001 1 777728 _ _ p244 p245) (mobiusTreeCheck_join cg 1200001 1 777856 _ _ p247 p248)) (mobiusTreeCheck_join cg 1200001 2 777984 _ _ (mobiusTreeCheck_join cg 1200001 1 777984 _ _ p251 p252) (mobiusTreeCheck_join cg 1200001 1 778112 _ _ p254 p255))))))) (mobiusTreeCheck_join cg 1200001 7 778240 _ _ (mobiusTreeCheck_join cg 1200001 6 778240 _ _ (mobiusTreeCheck_join cg 1200001 5 778240 _ _ (mobiusTreeCheck_join cg 1200001 4 778240 _ _ (mobiusTreeCheck_join cg 1200001 3 778240 _ _ (mobiusTreeCheck_join cg 1200001 2 778240 _ _ (mobiusTreeCheck_join cg 1200001 1 778240 _ _ p263 p264) (mobiusTreeCheck_join cg 1200001 1 778368 _ _ p266 p267)) (mobiusTreeCheck_join cg 1200001 2 778496 _ _ (mobiusTreeCheck_join cg 1200001 1 778496 _ _ p270 p271) (mobiusTreeCheck_join cg 1200001 1 778624 _ _ p273 p274))) (mobiusTreeCheck_join cg 1200001 3 778752 _ _ (mobiusTreeCheck_join cg 1200001 2 778752 _ _ (mobiusTreeCheck_join cg 1200001 1 778752 _ _ p278 p279) (mobiusTreeCheck_join cg 1200001 1 778880 _ _ p281 p282)) (mobiusTreeCheck_join cg 1200001 2 779008 _ _ (mobiusTreeCheck_join cg 1200001 1 779008 _ _ p285 p286) (mobiusTreeCheck_join cg 1200001 1 779136 _ _ p288 p289)))) (mobiusTreeCheck_join cg 1200001 4 779264 _ _ (mobiusTreeCheck_join cg 1200001 3 779264 _ _ (mobiusTreeCheck_join cg 1200001 2 779264 _ _ (mobiusTreeCheck_join cg 1200001 1 779264 _ _ p294 p295) (mobiusTreeCheck_join cg 1200001 1 779392 _ _ p297 p298)) (mobiusTreeCheck_join cg 1200001 2 779520 _ _ (mobiusTreeCheck_join cg 1200001 1 779520 _ _ p301 p302) (mobiusTreeCheck_join cg 1200001 1 779648 _ _ p304 p305))) (mobiusTreeCheck_join cg 1200001 3 779776 _ _ (mobiusTreeCheck_join cg 1200001 2 779776 _ _ (mobiusTreeCheck_join cg 1200001 1 779776 _ _ p309 p310) (mobiusTreeCheck_join cg 1200001 1 779904 _ _ p312 p313)) (mobiusTreeCheck_join cg 1200001 2 780032 _ _ (mobiusTreeCheck_join cg 1200001 1 780032 _ _ p316 p317) (mobiusTreeCheck_join cg 1200001 1 780160 _ _ p319 p320))))) (mobiusTreeCheck_join cg 1200001 5 780288 _ _ (mobiusTreeCheck_join cg 1200001 4 780288 _ _ (mobiusTreeCheck_join cg 1200001 3 780288 _ _ (mobiusTreeCheck_join cg 1200001 2 780288 _ _ (mobiusTreeCheck_join cg 1200001 1 780288 _ _ p326 p327) (mobiusTreeCheck_join cg 1200001 1 780416 _ _ p329 p330)) (mobiusTreeCheck_join cg 1200001 2 780544 _ _ (mobiusTreeCheck_join cg 1200001 1 780544 _ _ p333 p334) (mobiusTreeCheck_join cg 1200001 1 780672 _ _ p336 p337))) (mobiusTreeCheck_join cg 1200001 3 780800 _ _ (mobiusTreeCheck_join cg 1200001 2 780800 _ _ (mobiusTreeCheck_join cg 1200001 1 780800 _ _ p341 p342) (mobiusTreeCheck_join cg 1200001 1 780928 _ _ p344 p345)) (mobiusTreeCheck_join cg 1200001 2 781056 _ _ (mobiusTreeCheck_join cg 1200001 1 781056 _ _ p348 p349) (mobiusTreeCheck_join cg 1200001 1 781184 _ _ p351 p352)))) (mobiusTreeCheck_join cg 1200001 4 781312 _ _ (mobiusTreeCheck_join cg 1200001 3 781312 _ _ (mobiusTreeCheck_join cg 1200001 2 781312 _ _ (mobiusTreeCheck_join cg 1200001 1 781312 _ _ p357 p358) (mobiusTreeCheck_join cg 1200001 1 781440 _ _ p360 p361)) (mobiusTreeCheck_join cg 1200001 2 781568 _ _ (mobiusTreeCheck_join cg 1200001 1 781568 _ _ p364 p365) (mobiusTreeCheck_join cg 1200001 1 781696 _ _ p367 p368))) (mobiusTreeCheck_join cg 1200001 3 781824 _ _ (mobiusTreeCheck_join cg 1200001 2 781824 _ _ (mobiusTreeCheck_join cg 1200001 1 781824 _ _ p372 p373) (mobiusTreeCheck_join cg 1200001 1 781952 _ _ p375 p376)) (mobiusTreeCheck_join cg 1200001 2 782080 _ _ (mobiusTreeCheck_join cg 1200001 1 782080 _ _ p379 p380) (mobiusTreeCheck_join cg 1200001 1 782208 _ _ p382 p383)))))) (mobiusTreeCheck_join cg 1200001 6 782336 _ _ (mobiusTreeCheck_join cg 1200001 5 782336 _ _ (mobiusTreeCheck_join cg 1200001 4 782336 _ _ (mobiusTreeCheck_join cg 1200001 3 782336 _ _ (mobiusTreeCheck_join cg 1200001 2 782336 _ _ (mobiusTreeCheck_join cg 1200001 1 782336 _ _ p390 p391) (mobiusTreeCheck_join cg 1200001 1 782464 _ _ p393 p394)) (mobiusTreeCheck_join cg 1200001 2 782592 _ _ (mobiusTreeCheck_join cg 1200001 1 782592 _ _ p397 p398) (mobiusTreeCheck_join cg 1200001 1 782720 _ _ p400 p401))) (mobiusTreeCheck_join cg 1200001 3 782848 _ _ (mobiusTreeCheck_join cg 1200001 2 782848 _ _ (mobiusTreeCheck_join cg 1200001 1 782848 _ _ p405 p406) (mobiusTreeCheck_join cg 1200001 1 782976 _ _ p408 p409)) (mobiusTreeCheck_join cg 1200001 2 783104 _ _ (mobiusTreeCheck_join cg 1200001 1 783104 _ _ p412 p413) (mobiusTreeCheck_join cg 1200001 1 783232 _ _ p415 p416)))) (mobiusTreeCheck_join cg 1200001 4 783360 _ _ (mobiusTreeCheck_join cg 1200001 3 783360 _ _ (mobiusTreeCheck_join cg 1200001 2 783360 _ _ (mobiusTreeCheck_join cg 1200001 1 783360 _ _ p421 p422) (mobiusTreeCheck_join cg 1200001 1 783488 _ _ p424 p425)) (mobiusTreeCheck_join cg 1200001 2 783616 _ _ (mobiusTreeCheck_join cg 1200001 1 783616 _ _ p428 p429) (mobiusTreeCheck_join cg 1200001 1 783744 _ _ p431 p432))) (mobiusTreeCheck_join cg 1200001 3 783872 _ _ (mobiusTreeCheck_join cg 1200001 2 783872 _ _ (mobiusTreeCheck_join cg 1200001 1 783872 _ _ p436 p437) (mobiusTreeCheck_join cg 1200001 1 784000 _ _ p439 p440)) (mobiusTreeCheck_join cg 1200001 2 784128 _ _ (mobiusTreeCheck_join cg 1200001 1 784128 _ _ p443 p444) (mobiusTreeCheck_join cg 1200001 1 784256 _ _ p446 p447))))) (mobiusTreeCheck_join cg 1200001 5 784384 _ _ (mobiusTreeCheck_join cg 1200001 4 784384 _ _ (mobiusTreeCheck_join cg 1200001 3 784384 _ _ (mobiusTreeCheck_join cg 1200001 2 784384 _ _ (mobiusTreeCheck_join cg 1200001 1 784384 _ _ p453 p454) (mobiusTreeCheck_join cg 1200001 1 784512 _ _ p456 p457)) (mobiusTreeCheck_join cg 1200001 2 784640 _ _ (mobiusTreeCheck_join cg 1200001 1 784640 _ _ p460 p461) (mobiusTreeCheck_join cg 1200001 1 784768 _ _ p463 p464))) (mobiusTreeCheck_join cg 1200001 3 784896 _ _ (mobiusTreeCheck_join cg 1200001 2 784896 _ _ (mobiusTreeCheck_join cg 1200001 1 784896 _ _ p468 p469) (mobiusTreeCheck_join cg 1200001 1 785024 _ _ p471 p472)) (mobiusTreeCheck_join cg 1200001 2 785152 _ _ (mobiusTreeCheck_join cg 1200001 1 785152 _ _ p475 p476) (mobiusTreeCheck_join cg 1200001 1 785280 _ _ p478 p479)))) (mobiusTreeCheck_join cg 1200001 4 785408 _ _ (mobiusTreeCheck_join cg 1200001 3 785408 _ _ (mobiusTreeCheck_join cg 1200001 2 785408 _ _ (mobiusTreeCheck_join cg 1200001 1 785408 _ _ p484 p485) (mobiusTreeCheck_join cg 1200001 1 785536 _ _ p487 p488)) (mobiusTreeCheck_join cg 1200001 2 785664 _ _ (mobiusTreeCheck_join cg 1200001 1 785664 _ _ p491 p492) (mobiusTreeCheck_join cg 1200001 1 785792 _ _ p494 p495))) (mobiusTreeCheck_join cg 1200001 3 785920 _ _ (mobiusTreeCheck_join cg 1200001 2 785920 _ _ (mobiusTreeCheck_join cg 1200001 1 785920 _ _ p499 p500) (mobiusTreeCheck_join cg 1200001 1 786048 _ _ p502 p503)) (mobiusTreeCheck_join cg 1200001 2 786176 _ _ (mobiusTreeCheck_join cg 1200001 1 786176 _ _ p506 p507) (mobiusTreeCheck_join cg 1200001 1 786304 _ _ p509 p510))))))))

end Helfgott

open Helfgott
theorem solution : mobiusTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1200001 9 770048 (MobiusCertTree.branch mobiusTableBlock094 mobiusTableBlock095) = true := Helfgott.combined

#print axioms solution
