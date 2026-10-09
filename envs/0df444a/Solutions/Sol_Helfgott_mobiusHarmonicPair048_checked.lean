-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair048_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:52:42.455751+00:00
-- url     : https://prove2.me/submissions/815975b1-2853-443d-a3fd-a557d234fe99

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786432 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786496 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 4679042 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786560 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786624 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 4682098 d11 d12
private def d6 : MobiusHarmonicTree := .branch 9361140 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786688 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786752 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 4535175 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786816 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786880 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 4001997 d18 d19
private def d13 : MobiusHarmonicTree := .branch 8537172 d14 d17
private def d5 : MobiusHarmonicTree := .branch 17898312 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 786944 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787008 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 2510811 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787072 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787136 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 4576111 d26 d27
private def d21 : MobiusHarmonicTree := .branch 7086922 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787200 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787264 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 6158102 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787328 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787392 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 6216765 d33 d34
private def d28 : MobiusHarmonicTree := .branch 12374867 d29 d32
private def d20 : MobiusHarmonicTree := .branch 19461789 d21 d28
private def d4 : MobiusHarmonicTree := .branch 37360101 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787456 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787520 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 7801787 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787584 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787648 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 6657886 d42 d43
private def d37 : MobiusHarmonicTree := .branch 14459673 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787712 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787776 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 5652709 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787840 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787904 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 5343334 d49 d50
private def d44 : MobiusHarmonicTree := .branch 10996043 d45 d48
private def d36 : MobiusHarmonicTree := .branch 25455716 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 787968 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788032 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 6865276 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788096 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788160 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 6982153 d57 d58
private def d52 : MobiusHarmonicTree := .branch 13847429 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788224 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788288 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 6066406 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788352 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788416 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 3886376 d64 d65
private def d59 : MobiusHarmonicTree := .branch 9952782 d60 d63
private def d51 : MobiusHarmonicTree := .branch 23800211 d52 d59
private def d35 : MobiusHarmonicTree := .branch 49255927 d36 d51
private def d3 : MobiusHarmonicTree := .branch 86616028 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788480 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788544 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 1589096 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788608 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788672 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 769712 d74 d75
private def d69 : MobiusHarmonicTree := .branch 2358808 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788736 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788800 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 722678 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788864 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788928 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 1540097 d81 d82
private def d76 : MobiusHarmonicTree := .branch 2262775 d77 d80
private def d68 : MobiusHarmonicTree := .branch 4621583 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 788992 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789056 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 3283735 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789120 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789184 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 4328618 d89 d90
private def d84 : MobiusHarmonicTree := .branch 7612353 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789248 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789312 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 2759455 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789376 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789440 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 1079345 d96 d97
private def d91 : MobiusHarmonicTree := .branch 3838800 d92 d95
private def d83 : MobiusHarmonicTree := .branch 11451153 d84 d91
private def d67 : MobiusHarmonicTree := .branch 16072736 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789504 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789568 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 740980 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789632 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789696 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 1428477 d105 d106
private def d100 : MobiusHarmonicTree := .branch 2169457 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789760 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789824 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 568548 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789888 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 789952 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 827966 d112 d113
private def d107 : MobiusHarmonicTree := .branch 1396514 d108 d111
private def d99 : MobiusHarmonicTree := .branch 3565971 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790016 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790080 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 297477 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790144 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790208 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 699851 d120 d121
private def d115 : MobiusHarmonicTree := .branch 997328 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790272 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790336 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 2577456 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790400 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790464 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 1239856 d127 d128
private def d122 : MobiusHarmonicTree := .branch 3817312 d123 d126
private def d114 : MobiusHarmonicTree := .branch 4814640 d115 d122
private def d98 : MobiusHarmonicTree := .branch 8380611 d99 d114
private def d66 : MobiusHarmonicTree := .branch 24453347 d67 d98
private def d2 : MobiusHarmonicTree := .branch 111069375 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790528 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790592 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 1490066 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790656 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790720 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 1459504 d138 d139
private def d133 : MobiusHarmonicTree := .branch 2949570 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790784 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790848 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 368026 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790912 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 790976 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 998817 d145 d146
private def d140 : MobiusHarmonicTree := .branch 1366843 d141 d144
private def d132 : MobiusHarmonicTree := .branch 4316413 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791040 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791104 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 1722952 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791168 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791232 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 3149582 d153 d154
private def d148 : MobiusHarmonicTree := .branch 4872534 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791296 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791360 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 3329800 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791424 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791488 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 1549069 d160 d161
private def d155 : MobiusHarmonicTree := .branch 4878869 d156 d159
private def d147 : MobiusHarmonicTree := .branch 9751403 d148 d155
private def d131 : MobiusHarmonicTree := .branch 14067816 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791552 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791616 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 303238 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791680 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791744 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 1854156 d169 d170
private def d164 : MobiusHarmonicTree := .branch 2157394 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791808 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791872 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 3985571 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 791936 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792000 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 3222297 d176 d177
private def d171 : MobiusHarmonicTree := .branch 7207868 d172 d175
private def d163 : MobiusHarmonicTree := .branch 9365262 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792064 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792128 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 3754494 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792192 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792256 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 4788958 d184 d185
private def d179 : MobiusHarmonicTree := .branch 8543452 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792320 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792384 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 2848431 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792448 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792512 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 3645427 d191 d192
private def d186 : MobiusHarmonicTree := .branch 6493858 d187 d190
private def d178 : MobiusHarmonicTree := .branch 15037310 d179 d186
private def d162 : MobiusHarmonicTree := .branch 24402572 d163 d178
private def d130 : MobiusHarmonicTree := .branch 38470388 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792576 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792640 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 1746144 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792704 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792768 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 1404016 d201 d202
private def d196 : MobiusHarmonicTree := .branch 3150160 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792832 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792896 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 647074 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 792960 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793024 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 1199251 d208 d209
private def d203 : MobiusHarmonicTree := .branch 1846325 d204 d207
private def d195 : MobiusHarmonicTree := .branch 4996485 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793088 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793152 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 3363834 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793216 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793280 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 4354150 d216 d217
private def d211 : MobiusHarmonicTree := .branch 7717984 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793344 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793408 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 4156816 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793472 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793536 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 2066790 d223 d224
private def d218 : MobiusHarmonicTree := .branch 6223606 d219 d222
private def d210 : MobiusHarmonicTree := .branch 13941590 d211 d218
private def d194 : MobiusHarmonicTree := .branch 18938075 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793600 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793664 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 1169331 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793728 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793792 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 379252 d232 d233
private def d227 : MobiusHarmonicTree := .branch 1548583 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793856 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793920 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 317465 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 793984 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794048 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 2683740 d239 d240
private def d234 : MobiusHarmonicTree := .branch 3001205 d235 d238
private def d226 : MobiusHarmonicTree := .branch 4549788 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794112 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794176 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 5566790 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794240 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794304 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 5605003 d247 d248
private def d242 : MobiusHarmonicTree := .branch 11171793 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794368 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794432 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 4647409 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794496 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock096 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794560 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 6075116 d254 d255
private def d249 : MobiusHarmonicTree := .branch 10722525 d250 d253
private def d241 : MobiusHarmonicTree := .branch 21894318 d242 d249
private def d225 : MobiusHarmonicTree := .branch 26444106 d226 d241
private def d193 : MobiusHarmonicTree := .branch 45382181 d194 d225
private def d129 : MobiusHarmonicTree := .branch 83852569 d130 d193
private def d1 : MobiusHarmonicTree := .branch 194921944 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794624 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794688 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 5012099 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794752 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794816 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 5184939 d266 d267
private def d261 : MobiusHarmonicTree := .branch 10197038 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794880 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 794944 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 3211614 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795008 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795072 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 2597314 d273 d274
private def d268 : MobiusHarmonicTree := .branch 5808928 d269 d272
private def d260 : MobiusHarmonicTree := .branch 16005966 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795136 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795200 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 4334812 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795264 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795328 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 4781714 d281 d282
private def d276 : MobiusHarmonicTree := .branch 9116526 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795392 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795456 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 4462909 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795520 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795584 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 5671357 d288 d289
private def d283 : MobiusHarmonicTree := .branch 10134266 d284 d287
private def d275 : MobiusHarmonicTree := .branch 19250792 d276 d283
private def d259 : MobiusHarmonicTree := .branch 35256758 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795648 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795712 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 7622151 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795776 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795840 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 8264284 d297 d298
private def d292 : MobiusHarmonicTree := .branch 15886435 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795904 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 795968 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 8659952 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796032 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796096 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 6436507 d304 d305
private def d299 : MobiusHarmonicTree := .branch 15096459 d300 d303
private def d291 : MobiusHarmonicTree := .branch 30982894 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796160 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796224 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 5884105 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796288 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796352 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 6042604 d312 d313
private def d307 : MobiusHarmonicTree := .branch 11926709 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796416 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796480 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 6669427 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796544 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796608 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 7572160 d319 d320
private def d314 : MobiusHarmonicTree := .branch 14241587 d315 d318
private def d306 : MobiusHarmonicTree := .branch 26168296 d307 d314
private def d290 : MobiusHarmonicTree := .branch 57151190 d291 d306
private def d258 : MobiusHarmonicTree := .branch 92407948 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796672 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796736 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 7821973 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796800 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796864 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 8443170 d329 d330
private def d324 : MobiusHarmonicTree := .branch 16265143 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796928 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 796992 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 10538407 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797056 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797120 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 12102407 d336 d337
private def d331 : MobiusHarmonicTree := .branch 22640814 d332 d335
private def d323 : MobiusHarmonicTree := .branch 38905957 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797184 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797248 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 11366680 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797312 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797376 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 10655019 d344 d345
private def d339 : MobiusHarmonicTree := .branch 22021699 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797440 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797504 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 10539212 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797568 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797632 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 11786227 d351 d352
private def d346 : MobiusHarmonicTree := .branch 22325439 d347 d350
private def d338 : MobiusHarmonicTree := .branch 44347138 d339 d346
private def d322 : MobiusHarmonicTree := .branch 83253095 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797696 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797760 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 11430820 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797824 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797888 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 10967795 d360 d361
private def d355 : MobiusHarmonicTree := .branch 22398615 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 797952 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798016 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 10745468 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798080 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798144 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 11105853 d367 d368
private def d362 : MobiusHarmonicTree := .branch 21851321 d363 d366
private def d354 : MobiusHarmonicTree := .branch 44249936 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798208 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798272 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 10590485 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798336 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798400 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 7814462 d375 d376
private def d370 : MobiusHarmonicTree := .branch 18404947 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798464 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798528 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 8388001 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798592 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798656 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 8708427 d382 d383
private def d377 : MobiusHarmonicTree := .branch 17096428 d378 d381
private def d369 : MobiusHarmonicTree := .branch 35501375 d370 d377
private def d353 : MobiusHarmonicTree := .branch 79751311 d354 d369
private def d321 : MobiusHarmonicTree := .branch 163004406 d322 d353
private def d257 : MobiusHarmonicTree := .branch 255412354 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798720 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798784 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 9505767 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798848 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798912 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 8859589 d393 d394
private def d388 : MobiusHarmonicTree := .branch 18365356 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 798976 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799040 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 8338846 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799104 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799168 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 6127721 d400 d401
private def d395 : MobiusHarmonicTree := .branch 14466567 d396 d399
private def d387 : MobiusHarmonicTree := .branch 32831923 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799232 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799296 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 3630788 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799360 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799424 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 2648223 d408 d409
private def d403 : MobiusHarmonicTree := .branch 6279011 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799488 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799552 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 2517729 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799616 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799680 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 3719047 d415 d416
private def d410 : MobiusHarmonicTree := .branch 6236776 d411 d414
private def d402 : MobiusHarmonicTree := .branch 12515787 d403 d410
private def d386 : MobiusHarmonicTree := .branch 45347710 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799744 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799808 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 4396127 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799872 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 799936 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 3704143 d424 d425
private def d419 : MobiusHarmonicTree := .branch 8100270 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800000 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800064 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 3283542 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800128 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800192 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 4780154 d431 d432
private def d426 : MobiusHarmonicTree := .branch 8063696 d427 d430
private def d418 : MobiusHarmonicTree := .branch 16163966 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800256 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800320 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 5520337 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800384 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800448 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 6300276 d439 d440
private def d434 : MobiusHarmonicTree := .branch 11820613 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800512 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800576 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 6286825 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800640 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800704 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 8261489 d446 d447
private def d441 : MobiusHarmonicTree := .branch 14548314 d442 d445
private def d433 : MobiusHarmonicTree := .branch 26368927 d434 d441
private def d417 : MobiusHarmonicTree := .branch 42532893 d418 d433
private def d385 : MobiusHarmonicTree := .branch 87880603 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800768 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800832 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 8890847 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800896 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 800960 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 7446143 d456 d457
private def d451 : MobiusHarmonicTree := .branch 16336990 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801024 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801088 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 8337448 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801152 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801216 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 8789223 d463 d464
private def d458 : MobiusHarmonicTree := .branch 17126671 d459 d462
private def d450 : MobiusHarmonicTree := .branch 33463661 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801280 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801344 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 9047379 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801408 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801472 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 8596731 d471 d472
private def d466 : MobiusHarmonicTree := .branch 17644110 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801536 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801600 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 9917711 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801664 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801728 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 10170603 d478 d479
private def d473 : MobiusHarmonicTree := .branch 20088314 d474 d477
private def d465 : MobiusHarmonicTree := .branch 37732424 d466 d473
private def d449 : MobiusHarmonicTree := .branch 71196085 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801792 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801856 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 11348740 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801920 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 801984 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 9979069 d487 d488
private def d482 : MobiusHarmonicTree := .branch 21327809 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802048 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802112 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 10321570 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802176 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802240 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 10853440 d494 d495
private def d489 : MobiusHarmonicTree := .branch 21175010 d490 d493
private def d481 : MobiusHarmonicTree := .branch 42502819 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802304 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802368 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 10302089 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802432 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802496 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 8290482 d502 d503
private def d497 : MobiusHarmonicTree := .branch 18592571 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802560 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802624 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 7856770 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802688 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock097 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 802752 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 8787330 d509 d510
private def d504 : MobiusHarmonicTree := .branch 16644100 d505 d508
private def d496 : MobiusHarmonicTree := .branch 35236671 d497 d504
private def d480 : MobiusHarmonicTree := .branch 77739490 d481 d496
private def d448 : MobiusHarmonicTree := .branch 148935575 d449 d480
private def d384 : MobiusHarmonicTree := .branch 236816178 d385 d448
private def d256 : MobiusHarmonicTree := .branch 492228532 d257 d384
private def d0 : MobiusHarmonicTree := .branch 687150476 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 786432 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 786432 687150476 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 786432 194921944 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 786432 111069375 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 786432 86616028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 786432 37360101 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 786432 17898312 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 786432 9361140 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 786432 4679042 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 786560 4682098 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 786688 8537172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 786688 4535175 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 786816 4001997 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 786944 19461789 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 786944 7086922 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 786944 2510811 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 787072 4576111 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 787200 12374867 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 787200 6158102 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 787328 6216765 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 787456 49255927 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 787456 25455716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 787456 14459673 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 787456 7801787 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 787584 6657886 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 787712 10996043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 787712 5652709 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 787840 5343334 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 787968 23800211 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 787968 13847429 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 787968 6865276 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 788096 6982153 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 788224 9952782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 788224 6066406 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 788352 3886376 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 788480 24453347 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 788480 16072736 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 788480 4621583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 788480 2358808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 788480 1589096 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 788608 769712 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 788736 2262775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 788736 722678 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 788864 1540097 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 788992 11451153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 788992 7612353 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 788992 3283735 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 789120 4328618 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 789248 3838800 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 789248 2759455 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 789376 1079345 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 789504 8380611 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 789504 3565971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 789504 2169457 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 789504 740980 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 789632 1428477 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 789760 1396514 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 789760 568548 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 789888 827966 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 790016 4814640 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 790016 997328 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 790016 297477 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 790144 699851 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 790272 3817312 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 790272 2577456 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 790400 1239856 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 790528 83852569 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 790528 38470388 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 790528 14067816 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 790528 4316413 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 790528 2949570 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 790528 1490066 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 790656 1459504 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 790784 1366843 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 790784 368026 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 790912 998817 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 791040 9751403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 791040 4872534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 791040 1722952 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 791168 3149582 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 791296 4878869 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 791296 3329800 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 791424 1549069 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 791552 24402572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 791552 9365262 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 791552 2157394 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 791552 303238 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 791680 1854156 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 791808 7207868 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 791808 3985571 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 791936 3222297 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 792064 15037310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 792064 8543452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 792064 3754494 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 792192 4788958 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 792320 6493858 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 792320 2848431 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 792448 3645427 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 792576 45382181 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 792576 18938075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 792576 4996485 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 792576 3150160 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 792576 1746144 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 792704 1404016 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 792832 1846325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 792832 647074 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 792960 1199251 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 793088 13941590 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 793088 7717984 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 793088 3363834 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 793216 4354150 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 793344 6223606 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 793344 4156816 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 793472 2066790 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 793600 26444106 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 793600 4549788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 793600 1548583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 793600 1169331 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 793728 379252 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 793856 3001205 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 793856 317465 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 793984 2683740 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 794112 21894318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 794112 11171793 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 794112 5566790 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 794240 5605003 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 794368 10722525 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 794368 4647409 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 794496 6075116 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 794624 492228532 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 794624 255412354 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 794624 92407948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 794624 35256758 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 794624 16005966 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 794624 10197038 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 794624 5012099 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 794752 5184939 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 794880 5808928 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 794880 3211614 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 795008 2597314 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 795136 19250792 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 795136 9116526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 795136 4334812 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 795264 4781714 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 795392 10134266 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 795392 4462909 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 795520 5671357 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 795648 57151190 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 795648 30982894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 795648 15886435 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 795648 7622151 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 795776 8264284 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 795904 15096459 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 795904 8659952 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 796032 6436507 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 796160 26168296 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 796160 11926709 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 796160 5884105 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 796288 6042604 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 796416 14241587 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 796416 6669427 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 796544 7572160 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 796672 163004406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 796672 83253095 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 796672 38905957 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 796672 16265143 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 796672 7821973 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 796800 8443170 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 796928 22640814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 796928 10538407 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 797056 12102407 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 797184 44347138 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 797184 22021699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 797184 11366680 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 797312 10655019 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 797440 22325439 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 797440 10539212 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 797568 11786227 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 797696 79751311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 797696 44249936 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 797696 22398615 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 797696 11430820 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 797824 10967795 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 797952 21851321 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 797952 10745468 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 798080 11105853 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 798208 35501375 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 798208 18404947 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 798208 10590485 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 798336 7814462 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 798464 17096428 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 798464 8388001 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 798592 8708427 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 798720 236816178 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 798720 87880603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 798720 45347710 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 798720 32831923 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 798720 18365356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 798720 9505767 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 798848 8859589 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 798976 14466567 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 798976 8338846 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 799104 6127721 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 799232 12515787 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 799232 6279011 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 799232 3630788 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 799360 2648223 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 799488 6236776 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 799488 2517729 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 799616 3719047 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 799744 42532893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 799744 16163966 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 799744 8100270 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 799744 4396127 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 799872 3704143 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 800000 8063696 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 800000 3283542 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 800128 4780154 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 800256 26368927 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 800256 11820613 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 800256 5520337 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 800384 6300276 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 800512 14548314 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 800512 6286825 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 800640 8261489 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 800768 148935575 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 800768 71196085 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 800768 33463661 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 800768 16336990 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 800768 8890847 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 800896 7446143 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 801024 17126671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 801024 8337448 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 801152 8789223 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 801280 37732424 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 801280 17644110 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 801280 9047379 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 801408 8596731 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 801536 20088314 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 801536 9917711 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 801664 10170603 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 801792 77739490 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 801792 42502819 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 801792 21327809 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 801792 11348740 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 801920 9979069 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 802048 21175010 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 802048 10321570 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 802176 10853440 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 802304 35236671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 802304 18592571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 802304 10302089 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 802432 8290482 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 802560 16644100 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 802560 7856770 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 802688 8787330 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 786432 (MobiusHarmonicTree.branch 687150476 mobiusHarmonicBlock096 mobiusHarmonicBlock097) = true := Helfgott.combined

#print axioms solution
