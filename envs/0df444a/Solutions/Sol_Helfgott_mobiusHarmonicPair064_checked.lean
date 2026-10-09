-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair064_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:51:48.411408+00:00
-- url     : https://prove2.me/submissions/99969286-ce55-4513-bd37-dd7e6b74c233

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048576 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048640 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 31056499 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048704 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048768 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 31445540 d11 d12
private def d6 : MobiusHarmonicTree := .branch 62502039 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048832 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048896 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 31891710 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048960 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049024 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 32230974 d18 d19
private def d13 : MobiusHarmonicTree := .branch 64122684 d14 d17
private def d5 : MobiusHarmonicTree := .branch 126624723 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049088 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049152 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 31891557 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049216 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049280 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 32175462 d26 d27
private def d21 : MobiusHarmonicTree := .branch 64067019 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049344 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049408 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 33069193 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049472 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049536 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 32434412 d33 d34
private def d28 : MobiusHarmonicTree := .branch 65503605 d29 d32
private def d20 : MobiusHarmonicTree := .branch 129570624 d21 d28
private def d4 : MobiusHarmonicTree := .branch 256195347 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049600 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049664 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 31718817 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049728 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049792 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 32711310 d42 d43
private def d37 : MobiusHarmonicTree := .branch 64430127 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049856 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049920 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 33357845 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1049984 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050048 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 33743285 d49 d50
private def d44 : MobiusHarmonicTree := .branch 67101130 d45 d48
private def d36 : MobiusHarmonicTree := .branch 131531257 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050112 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050176 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 34548573 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050240 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050304 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 34625301 d57 d58
private def d52 : MobiusHarmonicTree := .branch 69173874 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050368 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050432 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 33917559 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050496 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050560 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 34921438 d64 d65
private def d59 : MobiusHarmonicTree := .branch 68838997 d60 d63
private def d51 : MobiusHarmonicTree := .branch 138012871 d52 d59
private def d35 : MobiusHarmonicTree := .branch 269544128 d36 d51
private def d3 : MobiusHarmonicTree := .branch 525739475 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050624 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050688 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 36699822 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050752 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050816 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 36997983 d74 d75
private def d69 : MobiusHarmonicTree := .branch 73697805 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050880 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1050944 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 37677633 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051008 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051072 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 38185830 d81 d82
private def d76 : MobiusHarmonicTree := .branch 75863463 d77 d80
private def d68 : MobiusHarmonicTree := .branch 149561268 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051136 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051200 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 39609084 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051264 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051328 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 40542128 d89 d90
private def d84 : MobiusHarmonicTree := .branch 80151212 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051392 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051456 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 40829189 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051520 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051584 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 40587427 d96 d97
private def d91 : MobiusHarmonicTree := .branch 81416616 d92 d95
private def d83 : MobiusHarmonicTree := .branch 161567828 d84 d91
private def d67 : MobiusHarmonicTree := .branch 311129096 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051648 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051712 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 39908346 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051776 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051840 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 40985401 d105 d106
private def d100 : MobiusHarmonicTree := .branch 80893747 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051904 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1051968 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 42008020 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052032 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052096 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 42123608 d112 d113
private def d107 : MobiusHarmonicTree := .branch 84131628 d108 d111
private def d99 : MobiusHarmonicTree := .branch 165025375 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052160 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052224 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 42546160 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052288 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052352 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 42252101 d120 d121
private def d115 : MobiusHarmonicTree := .branch 84798261 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052416 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052480 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 41888788 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052544 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052608 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 40523228 d127 d128
private def d122 : MobiusHarmonicTree := .branch 82412016 d123 d126
private def d114 : MobiusHarmonicTree := .branch 167210277 d115 d122
private def d98 : MobiusHarmonicTree := .branch 332235652 d99 d114
private def d66 : MobiusHarmonicTree := .branch 643364748 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1169104223 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052672 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052736 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 40663665 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052800 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052864 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 40993954 d138 d139
private def d133 : MobiusHarmonicTree := .branch 81657619 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052928 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1052992 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 41858898 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053056 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053120 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 42356124 d145 d146
private def d140 : MobiusHarmonicTree := .branch 84215022 d141 d144
private def d132 : MobiusHarmonicTree := .branch 165872641 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053184 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053248 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 42754494 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053312 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053376 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 43403380 d153 d154
private def d148 : MobiusHarmonicTree := .branch 86157874 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053440 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053504 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 43719899 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053568 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053632 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 43033127 d160 d161
private def d155 : MobiusHarmonicTree := .branch 86753026 d156 d159
private def d147 : MobiusHarmonicTree := .branch 172910900 d148 d155
private def d131 : MobiusHarmonicTree := .branch 338783541 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053696 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053760 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 43901925 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053824 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053888 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 44682212 d169 d170
private def d164 : MobiusHarmonicTree := .branch 88584137 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1053952 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054016 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 46202424 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054080 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054144 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 45761395 d176 d177
private def d171 : MobiusHarmonicTree := .branch 91963819 d172 d175
private def d163 : MobiusHarmonicTree := .branch 180547956 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054208 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054272 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 45905685 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054336 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054400 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 46096440 d184 d185
private def d179 : MobiusHarmonicTree := .branch 92002125 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054464 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054528 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 44959550 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054592 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054656 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 44948400 d191 d192
private def d186 : MobiusHarmonicTree := .branch 89907950 d187 d190
private def d178 : MobiusHarmonicTree := .branch 181910075 d179 d186
private def d162 : MobiusHarmonicTree := .branch 362458031 d163 d178
private def d130 : MobiusHarmonicTree := .branch 701241572 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054720 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054784 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 45125896 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054848 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054912 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 44647425 d201 d202
private def d196 : MobiusHarmonicTree := .branch 89773321 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1054976 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055040 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 45062822 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055104 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055168 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 44946486 d208 d209
private def d203 : MobiusHarmonicTree := .branch 90009308 d204 d207
private def d195 : MobiusHarmonicTree := .branch 179782629 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055232 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055296 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 45608149 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055360 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055424 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 45088124 d216 d217
private def d211 : MobiusHarmonicTree := .branch 90696273 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055488 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055552 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 44647831 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055616 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055680 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 44311798 d223 d224
private def d218 : MobiusHarmonicTree := .branch 88959629 d219 d222
private def d210 : MobiusHarmonicTree := .branch 179655902 d211 d218
private def d194 : MobiusHarmonicTree := .branch 359438531 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055744 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055808 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 44680562 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055872 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1055936 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 44141033 d232 d233
private def d227 : MobiusHarmonicTree := .branch 88821595 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056000 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056064 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 43414115 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056128 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056192 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 44044150 d239 d240
private def d234 : MobiusHarmonicTree := .branch 87458265 d235 d238
private def d226 : MobiusHarmonicTree := .branch 176279860 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056256 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056320 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 44466731 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056384 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056448 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 44333549 d247 d248
private def d242 : MobiusHarmonicTree := .branch 88800280 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056512 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056576 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 42267755 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056640 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock128 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056704 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 42434858 d254 d255
private def d249 : MobiusHarmonicTree := .branch 84702613 d250 d253
private def d241 : MobiusHarmonicTree := .branch 173502893 d242 d249
private def d225 : MobiusHarmonicTree := .branch 349782753 d226 d241
private def d193 : MobiusHarmonicTree := .branch 709221284 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1410462856 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2579567079 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056768 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056832 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 42097605 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056896 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1056960 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 41797312 d266 d267
private def d261 : MobiusHarmonicTree := .branch 83894917 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057024 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057088 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 42199957 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057152 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057216 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 42497556 d273 d274
private def d268 : MobiusHarmonicTree := .branch 84697513 d269 d272
private def d260 : MobiusHarmonicTree := .branch 168592430 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057280 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057344 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 41588250 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057408 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057472 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 41808283 d281 d282
private def d276 : MobiusHarmonicTree := .branch 83396533 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057536 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057600 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 42298693 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057664 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057728 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 42500610 d288 d289
private def d283 : MobiusHarmonicTree := .branch 84799303 d284 d287
private def d275 : MobiusHarmonicTree := .branch 168195836 d276 d283
private def d259 : MobiusHarmonicTree := .branch 336788266 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057792 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057856 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 42706286 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057920 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1057984 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 42537586 d297 d298
private def d292 : MobiusHarmonicTree := .branch 85243872 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058048 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058112 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 41387961 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058176 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058240 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 41592712 d304 d305
private def d299 : MobiusHarmonicTree := .branch 82980673 d300 d303
private def d291 : MobiusHarmonicTree := .branch 168224545 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058304 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058368 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 42348307 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058432 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058496 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 43400335 d312 d313
private def d307 : MobiusHarmonicTree := .branch 85748642 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058560 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058624 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 42680970 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058688 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058752 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 41790822 d319 d320
private def d314 : MobiusHarmonicTree := .branch 84471792 d315 d318
private def d306 : MobiusHarmonicTree := .branch 170220434 d307 d314
private def d290 : MobiusHarmonicTree := .branch 338444979 d291 d306
private def d258 : MobiusHarmonicTree := .branch 675233245 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058816 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058880 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 40524971 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1058944 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059008 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 41881722 d329 d330
private def d324 : MobiusHarmonicTree := .branch 82406693 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059072 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059136 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 40758789 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059200 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059264 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 39843793 d336 d337
private def d331 : MobiusHarmonicTree := .branch 80602582 d332 d335
private def d323 : MobiusHarmonicTree := .branch 163009275 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059328 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059392 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 41116097 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059456 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059520 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 42550487 d344 d345
private def d339 : MobiusHarmonicTree := .branch 83666584 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059584 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059648 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 42142375 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059712 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059776 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 41981607 d351 d352
private def d346 : MobiusHarmonicTree := .branch 84123982 d347 d350
private def d338 : MobiusHarmonicTree := .branch 167790566 d339 d346
private def d322 : MobiusHarmonicTree := .branch 330799841 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059840 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059904 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 41634974 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1059968 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060032 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 41774307 d360 d361
private def d355 : MobiusHarmonicTree := .branch 83409281 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060096 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060160 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 40957106 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060224 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060288 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 39991107 d367 d368
private def d362 : MobiusHarmonicTree := .branch 80948213 d363 d366
private def d354 : MobiusHarmonicTree := .branch 164357494 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060352 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060416 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 40950042 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060480 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060544 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 41159143 d375 d376
private def d370 : MobiusHarmonicTree := .branch 82109185 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060608 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060672 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 42319467 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060736 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060800 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 41630921 d382 d383
private def d377 : MobiusHarmonicTree := .branch 83950388 d378 d381
private def d369 : MobiusHarmonicTree := .branch 166059573 d370 d377
private def d353 : MobiusHarmonicTree := .branch 330417067 d354 d369
private def d321 : MobiusHarmonicTree := .branch 661216908 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1336450153 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060864 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060928 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 43081227 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1060992 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061056 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 44020356 d393 d394
private def d388 : MobiusHarmonicTree := .branch 87101583 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061120 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061184 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 44120595 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061248 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061312 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 45059410 d400 d401
private def d395 : MobiusHarmonicTree := .branch 89180005 d396 d399
private def d387 : MobiusHarmonicTree := .branch 176281588 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061376 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061440 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 45319639 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061504 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061568 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 45398052 d408 d409
private def d403 : MobiusHarmonicTree := .branch 90717691 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061632 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061696 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 43311921 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061760 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061824 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 44593144 d415 d416
private def d410 : MobiusHarmonicTree := .branch 87905065 d411 d414
private def d402 : MobiusHarmonicTree := .branch 178622756 d403 d410
private def d386 : MobiusHarmonicTree := .branch 354904344 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061888 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1061952 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 44119775 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062016 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062080 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 45609621 d424 d425
private def d419 : MobiusHarmonicTree := .branch 89729396 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062144 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062208 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 46522989 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062272 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062336 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 47231833 d431 d432
private def d426 : MobiusHarmonicTree := .branch 93754822 d427 d430
private def d418 : MobiusHarmonicTree := .branch 183484218 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062400 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062464 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 48373475 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062528 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062592 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 49287110 d439 d440
private def d434 : MobiusHarmonicTree := .branch 97660585 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062656 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062720 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 49857992 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062784 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062848 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 49456836 d446 d447
private def d441 : MobiusHarmonicTree := .branch 99314828 d442 d445
private def d433 : MobiusHarmonicTree := .branch 196975413 d434 d441
private def d417 : MobiusHarmonicTree := .branch 380459631 d418 d433
private def d385 : MobiusHarmonicTree := .branch 735363975 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062912 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1062976 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 48694520 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063040 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063104 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 47714134 d456 d457
private def d451 : MobiusHarmonicTree := .branch 96408654 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063168 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063232 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 48071433 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063296 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063360 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 48446511 d463 d464
private def d458 : MobiusHarmonicTree := .branch 96517944 d459 d462
private def d450 : MobiusHarmonicTree := .branch 192926598 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063424 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063488 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 47630175 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063552 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063616 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 46100363 d471 d472
private def d466 : MobiusHarmonicTree := .branch 93730538 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063680 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063744 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 45759234 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063808 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063872 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 44041106 d478 d479
private def d473 : MobiusHarmonicTree := .branch 89800340 d474 d477
private def d465 : MobiusHarmonicTree := .branch 183530878 d466 d473
private def d449 : MobiusHarmonicTree := .branch 376457476 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1063936 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064000 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 43342189 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064064 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064128 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 44198710 d487 d488
private def d482 : MobiusHarmonicTree := .branch 87540899 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064192 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064256 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 44113515 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064320 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064384 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 45844428 d494 d495
private def d489 : MobiusHarmonicTree := .branch 89957943 d490 d493
private def d481 : MobiusHarmonicTree := .branch 177498842 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064448 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064512 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 46318019 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064576 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064640 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 46484339 d502 d503
private def d497 : MobiusHarmonicTree := .branch 92802358 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064704 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064768 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 46972750 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064832 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock129 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1064896 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 47922143 d509 d510
private def d504 : MobiusHarmonicTree := .branch 94894893 d505 d508
private def d496 : MobiusHarmonicTree := .branch 187697251 d497 d504
private def d480 : MobiusHarmonicTree := .branch 365196093 d481 d496
private def d448 : MobiusHarmonicTree := .branch 741653569 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1477017544 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2813467697 d257 d384
private def d0 : MobiusHarmonicTree := .branch 5393034776 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 1048576 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 1048576 5393034776 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 1048576 2579567079 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1048576 1169104223 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1048576 525739475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1048576 256195347 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1048576 126624723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1048576 62502039 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1048576 31056499 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1048704 31445540 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1048832 64122684 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1048832 31891710 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1048960 32230974 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1049088 129570624 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1049088 64067019 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1049088 31891557 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1049216 32175462 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1049344 65503605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1049344 33069193 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1049472 32434412 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1049600 269544128 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1049600 131531257 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1049600 64430127 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1049600 31718817 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1049728 32711310 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1049856 67101130 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1049856 33357845 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1049984 33743285 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1050112 138012871 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1050112 69173874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1050112 34548573 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1050240 34625301 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1050368 68838997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1050368 33917559 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1050496 34921438 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1050624 643364748 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1050624 311129096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1050624 149561268 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1050624 73697805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1050624 36699822 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1050752 36997983 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1050880 75863463 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1050880 37677633 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1051008 38185830 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1051136 161567828 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1051136 80151212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1051136 39609084 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1051264 40542128 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1051392 81416616 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1051392 40829189 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1051520 40587427 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1051648 332235652 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1051648 165025375 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1051648 80893747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1051648 39908346 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1051776 40985401 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1051904 84131628 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1051904 42008020 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1052032 42123608 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1052160 167210277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1052160 84798261 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1052160 42546160 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1052288 42252101 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1052416 82412016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1052416 41888788 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1052544 40523228 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1052672 1410462856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1052672 701241572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1052672 338783541 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1052672 165872641 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1052672 81657619 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1052672 40663665 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1052800 40993954 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1052928 84215022 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1052928 41858898 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1053056 42356124 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1053184 172910900 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1053184 86157874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1053184 42754494 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1053312 43403380 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1053440 86753026 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1053440 43719899 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1053568 43033127 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1053696 362458031 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1053696 180547956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1053696 88584137 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1053696 43901925 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1053824 44682212 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1053952 91963819 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1053952 46202424 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1054080 45761395 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1054208 181910075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1054208 92002125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1054208 45905685 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1054336 46096440 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1054464 89907950 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1054464 44959550 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1054592 44948400 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1054720 709221284 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1054720 359438531 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1054720 179782629 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1054720 89773321 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1054720 45125896 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1054848 44647425 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1054976 90009308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1054976 45062822 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1055104 44946486 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1055232 179655902 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1055232 90696273 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1055232 45608149 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1055360 45088124 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1055488 88959629 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1055488 44647831 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1055616 44311798 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1055744 349782753 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1055744 176279860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1055744 88821595 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1055744 44680562 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1055872 44141033 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1056000 87458265 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1056000 43414115 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1056128 44044150 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1056256 173502893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1056256 88800280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1056256 44466731 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1056384 44333549 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1056512 84702613 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1056512 42267755 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1056640 42434858 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 1056768 2813467697 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1056768 1336450153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1056768 675233245 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1056768 336788266 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1056768 168592430 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1056768 83894917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1056768 42097605 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1056896 41797312 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1057024 84697513 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1057024 42199957 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1057152 42497556 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1057280 168195836 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1057280 83396533 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1057280 41588250 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1057408 41808283 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1057536 84799303 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1057536 42298693 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1057664 42500610 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1057792 338444979 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1057792 168224545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1057792 85243872 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1057792 42706286 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1057920 42537586 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1058048 82980673 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1058048 41387961 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1058176 41592712 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1058304 170220434 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1058304 85748642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1058304 42348307 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1058432 43400335 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1058560 84471792 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1058560 42680970 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1058688 41790822 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1058816 661216908 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1058816 330799841 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1058816 163009275 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1058816 82406693 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1058816 40524971 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1058944 41881722 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1059072 80602582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1059072 40758789 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1059200 39843793 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1059328 167790566 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1059328 83666584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1059328 41116097 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1059456 42550487 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1059584 84123982 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1059584 42142375 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1059712 41981607 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1059840 330417067 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1059840 164357494 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1059840 83409281 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1059840 41634974 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1059968 41774307 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1060096 80948213 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1060096 40957106 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1060224 39991107 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1060352 166059573 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1060352 82109185 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1060352 40950042 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1060480 41159143 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1060608 83950388 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1060608 42319467 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1060736 41630921 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1060864 1477017544 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1060864 735363975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1060864 354904344 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1060864 176281588 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1060864 87101583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1060864 43081227 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1060992 44020356 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1061120 89180005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1061120 44120595 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1061248 45059410 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1061376 178622756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1061376 90717691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1061376 45319639 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1061504 45398052 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1061632 87905065 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1061632 43311921 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1061760 44593144 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1061888 380459631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1061888 183484218 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1061888 89729396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1061888 44119775 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1062016 45609621 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1062144 93754822 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1062144 46522989 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1062272 47231833 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1062400 196975413 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1062400 97660585 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1062400 48373475 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1062528 49287110 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1062656 99314828 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1062656 49857992 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1062784 49456836 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1062912 741653569 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1062912 376457476 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1062912 192926598 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1062912 96408654 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1062912 48694520 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1063040 47714134 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1063168 96517944 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1063168 48071433 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1063296 48446511 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1063424 183530878 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1063424 93730538 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1063424 47630175 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1063552 46100363 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1063680 89800340 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1063680 45759234 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1063808 44041106 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1063936 365196093 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1063936 177498842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1063936 87540899 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1063936 43342189 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1064064 44198710 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1064192 89957943 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1064192 44113515 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1064320 45844428 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1064448 187697251 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1064448 92802358 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1064448 46318019 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1064576 46484339 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1064704 94894893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1064704 46972750 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1064832 47922143 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 1048576 (MobiusHarmonicTree.branch 5393034776 mobiusHarmonicBlock128 mobiusHarmonicBlock129) = true := Helfgott.combined

#print axioms solution
