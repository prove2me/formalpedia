-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair009_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:24:43.257542+00:00
-- url     : https://prove2.me/submissions/cf4e98d4-cc08-4f5d-a572-236b671c416e

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusHarmonicTable1078853
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
private abbrev cm : ℕ → ℤ := mobiusPrefixValue 16 mobiusHarmonic1078853

private def publishedLeaf : ℕ → MobiusHarmonicTree → ℕ → MobiusHarmonicTree
  | 0, tree, _ => tree
  | d + 1, .branch _ l r, k =>
      if k < 2 ^ d then publishedLeaf d l k else publishedLeaf d r (k - 2 ^ d)
  | _, tree, _ => tree

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147456 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147520 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 50365930 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147584 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147648 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 51758744 d11 d12
private def d6 : MobiusHarmonicTree := .branch 102124674 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147712 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147776 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 55035708 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147840 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147904 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 54630771 d18 d19
private def d13 : MobiusHarmonicTree := .branch 109666479 d14 d17
private def d5 : MobiusHarmonicTree := .branch 211791153 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147968 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148032 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 52475510 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148096 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148160 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 50864068 d26 d27
private def d21 : MobiusHarmonicTree := .branch 103339578 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148224 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148288 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 49148683 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148352 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148416 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 39329007 d33 d34
private def d28 : MobiusHarmonicTree := .branch 88477690 d29 d32
private def d20 : MobiusHarmonicTree := .branch 191817268 d21 d28
private def d4 : MobiusHarmonicTree := .branch 403608421 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148480 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148544 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 39510667 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148608 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148672 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 35420289 d42 d43
private def d37 : MobiusHarmonicTree := .branch 74930956 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148736 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148800 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 40020289 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148864 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148928 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 43329572 d49 d50
private def d44 : MobiusHarmonicTree := .branch 83349861 d45 d48
private def d36 : MobiusHarmonicTree := .branch 158280817 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 148992 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149056 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 41527993 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149120 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149184 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 50943835 d57 d58
private def d52 : MobiusHarmonicTree := .branch 92471828 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149248 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149312 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 53786336 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149376 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149440 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 54202641 d64 d65
private def d59 : MobiusHarmonicTree := .branch 107988977 d60 d63
private def d51 : MobiusHarmonicTree := .branch 200460805 d52 d59
private def d35 : MobiusHarmonicTree := .branch 358741622 d36 d51
private def d3 : MobiusHarmonicTree := .branch 762350043 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149504 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149568 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 57833664 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149632 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149696 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 53896359 d74 d75
private def d69 : MobiusHarmonicTree := .branch 111730023 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149760 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149824 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 40702125 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149888 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 149952 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 44480867 d81 d82
private def d76 : MobiusHarmonicTree := .branch 85182992 d77 d80
private def d68 : MobiusHarmonicTree := .branch 196913015 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150016 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150080 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 41218195 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150144 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150208 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 47640035 d89 d90
private def d84 : MobiusHarmonicTree := .branch 88858230 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150272 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150336 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 54743948 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150400 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150464 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 50844344 d96 d97
private def d91 : MobiusHarmonicTree := .branch 105588292 d92 d95
private def d83 : MobiusHarmonicTree := .branch 194446522 d84 d91
private def d67 : MobiusHarmonicTree := .branch 391359537 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150528 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150592 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 43628199 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150656 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150720 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 35271119 d105 d106
private def d100 : MobiusHarmonicTree := .branch 78899318 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150784 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150848 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 32164934 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150912 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 150976 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 33734087 d112 d113
private def d107 : MobiusHarmonicTree := .branch 65899021 d108 d111
private def d99 : MobiusHarmonicTree := .branch 144798339 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151040 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151104 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 25540010 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151168 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151232 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 22442654 d120 d121
private def d115 : MobiusHarmonicTree := .branch 47982664 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151296 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151360 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 20434555 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151424 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151488 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 28127203 d127 d128
private def d122 : MobiusHarmonicTree := .branch 48561758 d123 d126
private def d114 : MobiusHarmonicTree := .branch 96544422 d115 d122
private def d98 : MobiusHarmonicTree := .branch 241342761 d99 d114
private def d66 : MobiusHarmonicTree := .branch 632702298 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1395052341 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151552 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151616 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 35101785 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151680 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151744 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 42545555 d138 d139
private def d133 : MobiusHarmonicTree := .branch 77647340 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151808 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151872 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 47256642 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 151936 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152000 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 51848853 d145 d146
private def d140 : MobiusHarmonicTree := .branch 99105495 d141 d144
private def d132 : MobiusHarmonicTree := .branch 176752835 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152064 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152128 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 61402462 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152192 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152256 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 64581980 d153 d154
private def d148 : MobiusHarmonicTree := .branch 125984442 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152320 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152384 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 65183528 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152448 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152512 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 69031919 d160 d161
private def d155 : MobiusHarmonicTree := .branch 134215447 d156 d159
private def d147 : MobiusHarmonicTree := .branch 260199889 d148 d155
private def d131 : MobiusHarmonicTree := .branch 436952724 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152576 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152640 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 65978096 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152704 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152768 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 73621289 d169 d170
private def d164 : MobiusHarmonicTree := .branch 139599385 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152832 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152896 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 80578145 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 152960 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153024 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 79236483 d176 d177
private def d171 : MobiusHarmonicTree := .branch 159814628 d172 d175
private def d163 : MobiusHarmonicTree := .branch 299414013 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153088 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153152 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 79405503 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153216 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153280 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 75619419 d184 d185
private def d179 : MobiusHarmonicTree := .branch 155024922 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153344 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153408 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 81541059 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153472 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153536 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 82411330 d191 d192
private def d186 : MobiusHarmonicTree := .branch 163952389 d187 d190
private def d178 : MobiusHarmonicTree := .branch 318977311 d179 d186
private def d162 : MobiusHarmonicTree := .branch 618391324 d163 d178
private def d130 : MobiusHarmonicTree := .branch 1055344048 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153600 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153664 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 80845499 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153728 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153792 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 81825197 d201 d202
private def d196 : MobiusHarmonicTree := .branch 162670696 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153856 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153920 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 81204727 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 153984 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154048 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 79137672 d208 d209
private def d203 : MobiusHarmonicTree := .branch 160342399 d204 d207
private def d195 : MobiusHarmonicTree := .branch 323013095 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154112 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154176 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 81926400 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154240 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154304 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 82934057 d216 d217
private def d211 : MobiusHarmonicTree := .branch 164860457 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154368 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154432 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 77504242 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154496 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154560 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 71157281 d223 d224
private def d218 : MobiusHarmonicTree := .branch 148661523 d219 d222
private def d210 : MobiusHarmonicTree := .branch 313521980 d211 d218
private def d194 : MobiusHarmonicTree := .branch 636535075 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154624 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154688 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 69896150 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154752 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154816 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 71349085 d232 d233
private def d227 : MobiusHarmonicTree := .branch 141245235 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154880 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 154944 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 72136421 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155008 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155072 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 66718362 d239 d240
private def d234 : MobiusHarmonicTree := .branch 138854783 d235 d238
private def d226 : MobiusHarmonicTree := .branch 280100018 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155136 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155200 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 56559293 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155264 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155328 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 61476637 d247 d248
private def d242 : MobiusHarmonicTree := .branch 118035930 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155392 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155456 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 51494805 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155520 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock018 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155584 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 52357938 d254 d255
private def d249 : MobiusHarmonicTree := .branch 103852743 d250 d253
private def d241 : MobiusHarmonicTree := .branch 221888673 d242 d249
private def d225 : MobiusHarmonicTree := .branch 501988691 d226 d241
private def d193 : MobiusHarmonicTree := .branch 1138523766 d194 d225
private def d129 : MobiusHarmonicTree := .branch 2193867814 d130 d193
private def d1 : MobiusHarmonicTree := .branch 3588920155 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155648 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155712 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 53137176 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155776 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155840 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 57763342 d266 d267
private def d261 : MobiusHarmonicTree := .branch 110900518 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155904 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 155968 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 55487066 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156032 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156096 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 51712172 d273 d274
private def d268 : MobiusHarmonicTree := .branch 107199238 d269 d272
private def d260 : MobiusHarmonicTree := .branch 218099756 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156160 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156224 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 45818958 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156288 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156352 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 46562220 d281 d282
private def d276 : MobiusHarmonicTree := .branch 92381178 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156416 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156480 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 41079364 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156544 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156608 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 31129156 d288 d289
private def d283 : MobiusHarmonicTree := .branch 72208520 d284 d287
private def d275 : MobiusHarmonicTree := .branch 164589698 d276 d283
private def d259 : MobiusHarmonicTree := .branch 382689454 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156672 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156736 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 34401580 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156800 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156864 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 40582911 d297 d298
private def d292 : MobiusHarmonicTree := .branch 74984491 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156928 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 156992 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 44116818 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157056 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157120 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 43827277 d304 d305
private def d299 : MobiusHarmonicTree := .branch 87944095 d300 d303
private def d291 : MobiusHarmonicTree := .branch 162928586 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157184 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157248 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 48972773 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157312 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157376 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 53388613 d312 d313
private def d307 : MobiusHarmonicTree := .branch 102361386 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157440 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157504 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 60474157 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157568 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157632 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 60114963 d319 d320
private def d314 : MobiusHarmonicTree := .branch 120589120 d315 d318
private def d306 : MobiusHarmonicTree := .branch 222950506 d307 d314
private def d290 : MobiusHarmonicTree := .branch 385879092 d291 d306
private def d258 : MobiusHarmonicTree := .branch 768568546 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157696 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157760 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 50419277 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157824 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157888 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 50579654 d329 d330
private def d324 : MobiusHarmonicTree := .branch 100998931 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 157952 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158016 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 56139744 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158080 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158144 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 56695468 d336 d337
private def d331 : MobiusHarmonicTree := .branch 112835212 d332 d335
private def d323 : MobiusHarmonicTree := .branch 213834143 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158208 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158272 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 58855077 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158336 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158400 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 59760110 d344 d345
private def d339 : MobiusHarmonicTree := .branch 118615187 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158464 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158528 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 58380749 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158592 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158656 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 60849860 d351 d352
private def d346 : MobiusHarmonicTree := .branch 119230609 d347 d350
private def d338 : MobiusHarmonicTree := .branch 237845796 d339 d346
private def d322 : MobiusHarmonicTree := .branch 451679939 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158720 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158784 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 54911162 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158848 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158912 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 51538440 d360 d361
private def d355 : MobiusHarmonicTree := .branch 106449602 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 158976 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159040 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 51917941 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159104 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159168 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 47578746 d367 d368
private def d362 : MobiusHarmonicTree := .branch 99496687 d363 d366
private def d354 : MobiusHarmonicTree := .branch 205946289 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159232 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159296 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 45940593 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159360 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159424 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 41725285 d375 d376
private def d370 : MobiusHarmonicTree := .branch 87665878 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159488 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159552 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 45019320 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159616 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159680 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 52705214 d382 d383
private def d377 : MobiusHarmonicTree := .branch 97724534 d378 d381
private def d369 : MobiusHarmonicTree := .branch 185390412 d370 d377
private def d353 : MobiusHarmonicTree := .branch 391336701 d354 d369
private def d321 : MobiusHarmonicTree := .branch 843016640 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1611585186 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159744 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159808 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 55729275 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159872 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 159936 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 59092933 d393 d394
private def d388 : MobiusHarmonicTree := .branch 114822208 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160000 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160064 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 52910370 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160128 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160192 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 47449760 d400 d401
private def d395 : MobiusHarmonicTree := .branch 100360130 d396 d399
private def d387 : MobiusHarmonicTree := .branch 215182338 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160256 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160320 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 41318373 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160384 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160448 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 35763400 d408 d409
private def d403 : MobiusHarmonicTree := .branch 77081773 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160512 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160576 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 30122542 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160640 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160704 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 41946213 d415 d416
private def d410 : MobiusHarmonicTree := .branch 72068755 d411 d414
private def d402 : MobiusHarmonicTree := .branch 149150528 d403 d410
private def d386 : MobiusHarmonicTree := .branch 364332866 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160768 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160832 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 46819353 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160896 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 160960 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 43452050 d424 d425
private def d419 : MobiusHarmonicTree := .branch 90271403 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161024 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161088 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 45708100 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161152 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161216 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 40871169 d431 d432
private def d426 : MobiusHarmonicTree := .branch 86579269 d427 d430
private def d418 : MobiusHarmonicTree := .branch 176850672 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161280 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161344 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 42983225 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161408 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161472 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 35425130 d439 d440
private def d434 : MobiusHarmonicTree := .branch 78408355 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161536 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161600 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 30817010 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161664 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161728 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 30408694 d446 d447
private def d441 : MobiusHarmonicTree := .branch 61225704 d442 d445
private def d433 : MobiusHarmonicTree := .branch 139634059 d434 d441
private def d417 : MobiusHarmonicTree := .branch 316484731 d418 d433
private def d385 : MobiusHarmonicTree := .branch 680817597 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161792 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161856 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 30632754 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161920 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 161984 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 30564715 d456 d457
private def d451 : MobiusHarmonicTree := .branch 61197469 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162048 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162112 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 21319866 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162176 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162240 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 5344037 d463 d464
private def d458 : MobiusHarmonicTree := .branch 26663903 d459 d462
private def d450 : MobiusHarmonicTree := .branch 87861372 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162304 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162368 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 2525642 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162432 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162496 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 4873414 d471 d472
private def d466 : MobiusHarmonicTree := .branch 7399056 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162560 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162624 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 9629242 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162688 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162752 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 17940992 d478 d479
private def d473 : MobiusHarmonicTree := .branch 27570234 d474 d477
private def d465 : MobiusHarmonicTree := .branch 34969290 d466 d473
private def d449 : MobiusHarmonicTree := .branch 122830662 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162816 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162880 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 23532295 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 162944 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163008 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 22532960 d487 d488
private def d482 : MobiusHarmonicTree := .branch 46065255 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163072 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163136 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 6847975 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163200 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163264 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 4655674 d494 d495
private def d489 : MobiusHarmonicTree := .branch 11503649 d490 d493
private def d481 : MobiusHarmonicTree := .branch 57568904 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163328 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163392 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 4143273 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163456 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163520 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 7564410 d502 d503
private def d497 : MobiusHarmonicTree := .branch 11707683 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163584 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163648 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 4895731 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163712 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock019 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163776 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 3553464 d509 d510
private def d504 : MobiusHarmonicTree := .branch 8449195 d505 d508
private def d496 : MobiusHarmonicTree := .branch 20156878 d497 d504
private def d480 : MobiusHarmonicTree := .branch 77725782 d481 d496
private def d448 : MobiusHarmonicTree := .branch 200556444 d449 d480
private def d384 : MobiusHarmonicTree := .branch 881374041 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2492959227 d257 d384
private def d0 : MobiusHarmonicTree := .branch 6081879382 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 147456 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 147456 6081879382 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 147456 3588920155 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 147456 1395052341 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 147456 762350043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 147456 403608421 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 147456 211791153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 147456 102124674 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 147456 50365930 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 147584 51758744 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 147712 109666479 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 147712 55035708 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 147840 54630771 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 147968 191817268 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 147968 103339578 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 147968 52475510 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 148096 50864068 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 148224 88477690 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 148224 49148683 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 148352 39329007 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 148480 358741622 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 148480 158280817 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 148480 74930956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 148480 39510667 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 148608 35420289 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 148736 83349861 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 148736 40020289 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 148864 43329572 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 148992 200460805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 148992 92471828 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 148992 41527993 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 149120 50943835 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 149248 107988977 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 149248 53786336 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 149376 54202641 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 149504 632702298 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 149504 391359537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 149504 196913015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 149504 111730023 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 149504 57833664 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 149632 53896359 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 149760 85182992 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 149760 40702125 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 149888 44480867 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 150016 194446522 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 150016 88858230 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 150016 41218195 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 150144 47640035 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 150272 105588292 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 150272 54743948 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 150400 50844344 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 150528 241342761 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 150528 144798339 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 150528 78899318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 150528 43628199 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 150656 35271119 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 150784 65899021 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 150784 32164934 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 150912 33734087 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 151040 96544422 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 151040 47982664 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 151040 25540010 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 151168 22442654 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 151296 48561758 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 151296 20434555 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 151424 28127203 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 151552 2193867814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 151552 1055344048 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 151552 436952724 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 151552 176752835 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 151552 77647340 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 151552 35101785 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 151680 42545555 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 151808 99105495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 151808 47256642 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 151936 51848853 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 152064 260199889 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 152064 125984442 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 152064 61402462 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 152192 64581980 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 152320 134215447 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 152320 65183528 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 152448 69031919 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 152576 618391324 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 152576 299414013 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 152576 139599385 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 152576 65978096 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 152704 73621289 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 152832 159814628 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 152832 80578145 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 152960 79236483 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 153088 318977311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 153088 155024922 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 153088 79405503 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 153216 75619419 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 153344 163952389 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 153344 81541059 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 153472 82411330 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 153600 1138523766 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 153600 636535075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 153600 323013095 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 153600 162670696 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 153600 80845499 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 153728 81825197 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 153856 160342399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 153856 81204727 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 153984 79137672 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 154112 313521980 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 154112 164860457 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 154112 81926400 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 154240 82934057 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 154368 148661523 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 154368 77504242 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 154496 71157281 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 154624 501988691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 154624 280100018 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 154624 141245235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 154624 69896150 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 154752 71349085 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 154880 138854783 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 154880 72136421 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 155008 66718362 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 155136 221888673 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 155136 118035930 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 155136 56559293 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 155264 61476637 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 155392 103852743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 155392 51494805 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 155520 52357938 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 155648 2492959227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 155648 1611585186 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 155648 768568546 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 155648 382689454 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 155648 218099756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 155648 110900518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 155648 53137176 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 155776 57763342 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 155904 107199238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 155904 55487066 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 156032 51712172 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 156160 164589698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 156160 92381178 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 156160 45818958 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 156288 46562220 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 156416 72208520 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 156416 41079364 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 156544 31129156 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 156672 385879092 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 156672 162928586 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 156672 74984491 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 156672 34401580 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 156800 40582911 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 156928 87944095 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 156928 44116818 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 157056 43827277 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 157184 222950506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 157184 102361386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 157184 48972773 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 157312 53388613 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 157440 120589120 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 157440 60474157 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 157568 60114963 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 157696 843016640 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 157696 451679939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 157696 213834143 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 157696 100998931 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 157696 50419277 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 157824 50579654 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 157952 112835212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 157952 56139744 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 158080 56695468 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 158208 237845796 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 158208 118615187 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 158208 58855077 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 158336 59760110 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 158464 119230609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 158464 58380749 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 158592 60849860 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 158720 391336701 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 158720 205946289 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 158720 106449602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 158720 54911162 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 158848 51538440 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 158976 99496687 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 158976 51917941 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 159104 47578746 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 159232 185390412 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 159232 87665878 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 159232 45940593 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 159360 41725285 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 159488 97724534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 159488 45019320 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 159616 52705214 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 159744 881374041 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 159744 680817597 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 159744 364332866 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 159744 215182338 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 159744 114822208 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 159744 55729275 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 159872 59092933 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 160000 100360130 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 160000 52910370 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 160128 47449760 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 160256 149150528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 160256 77081773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 160256 41318373 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 160384 35763400 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 160512 72068755 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 160512 30122542 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 160640 41946213 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 160768 316484731 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 160768 176850672 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 160768 90271403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 160768 46819353 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 160896 43452050 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 161024 86579269 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 161024 45708100 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 161152 40871169 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 161280 139634059 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 161280 78408355 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 161280 42983225 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 161408 35425130 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 161536 61225704 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 161536 30817010 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 161664 30408694 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 161792 200556444 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 161792 122830662 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 161792 87861372 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 161792 61197469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 161792 30632754 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 161920 30564715 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 162048 26663903 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 162048 21319866 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 162176 5344037 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 162304 34969290 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 162304 7399056 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 162304 2525642 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 162432 4873414 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 162560 27570234 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 162560 9629242 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 162688 17940992 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 162816 77725782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 162816 57568904 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 162816 46065255 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 162816 23532295 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 162944 22532960 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 163072 11503649 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 163072 6847975 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 163200 4655674 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 163328 20156878 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 163328 11707683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 163328 4143273 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 163456 7564410 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 163584 8449195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 163584 4895731 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 163712 3553464 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 147456 (MobiusHarmonicTree.branch 6081879382 mobiusHarmonicBlock018 mobiusHarmonicBlock019) = true := Helfgott.combined

#print axioms solution
