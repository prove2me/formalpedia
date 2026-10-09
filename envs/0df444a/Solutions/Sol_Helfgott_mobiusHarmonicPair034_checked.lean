-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair034_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:03:14.57801+00:00
-- url     : https://prove2.me/submissions/eda42977-ad82-41e6-8eee-a84e1e1b863f

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557056 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557120 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 1373140 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557184 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557248 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 3895925 d11 d12
private def d6 : MobiusHarmonicTree := .branch 5269065 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557312 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557376 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 5911634 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557440 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557504 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 9081589 d18 d19
private def d13 : MobiusHarmonicTree := .branch 14993223 d14 d17
private def d5 : MobiusHarmonicTree := .branch 20262288 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557568 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557632 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 10063999 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557696 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557760 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 10653460 d26 d27
private def d21 : MobiusHarmonicTree := .branch 20717459 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557824 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557888 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 11570489 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 557952 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558016 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 10822345 d33 d34
private def d28 : MobiusHarmonicTree := .branch 22392834 d29 d32
private def d20 : MobiusHarmonicTree := .branch 43110293 d21 d28
private def d4 : MobiusHarmonicTree := .branch 63372581 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558080 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558144 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 11583093 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558208 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558272 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 10496788 d42 d43
private def d37 : MobiusHarmonicTree := .branch 22079881 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558336 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558400 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 11694169 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558464 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558528 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 10604811 d49 d50
private def d44 : MobiusHarmonicTree := .branch 22298980 d45 d48
private def d36 : MobiusHarmonicTree := .branch 44378861 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558592 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558656 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 8237693 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558720 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558784 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 7405463 d57 d58
private def d52 : MobiusHarmonicTree := .branch 15643156 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558848 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558912 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 6187072 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 558976 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559040 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 6641823 d64 d65
private def d59 : MobiusHarmonicTree := .branch 12828895 d60 d63
private def d51 : MobiusHarmonicTree := .branch 28472051 d52 d59
private def d35 : MobiusHarmonicTree := .branch 72850912 d36 d51
private def d3 : MobiusHarmonicTree := .branch 136223493 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559104 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559168 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 7614911 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559232 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559296 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 7522030 d74 d75
private def d69 : MobiusHarmonicTree := .branch 15136941 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559360 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559424 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 5816795 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559488 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559552 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 2312687 d81 d82
private def d76 : MobiusHarmonicTree := .branch 8129482 d77 d80
private def d68 : MobiusHarmonicTree := .branch 23266423 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559616 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559680 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 616506 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559744 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559808 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 602042 d89 d90
private def d84 : MobiusHarmonicTree := .branch 1218548 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559872 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 559936 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 2093130 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560000 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560064 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 2217651 d96 d97
private def d91 : MobiusHarmonicTree := .branch 4310781 d92 d95
private def d83 : MobiusHarmonicTree := .branch 5529329 d84 d91
private def d67 : MobiusHarmonicTree := .branch 28795752 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560128 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560192 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 3993259 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560256 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560320 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 5720002 d105 d106
private def d100 : MobiusHarmonicTree := .branch 9713261 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560384 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560448 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 5233355 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560512 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560576 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 5474779 d112 d113
private def d107 : MobiusHarmonicTree := .branch 10708134 d108 d111
private def d99 : MobiusHarmonicTree := .branch 20421395 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560640 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560704 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 5243481 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560768 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560832 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 7840118 d120 d121
private def d115 : MobiusHarmonicTree := .branch 13083599 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560896 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 560960 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 10430399 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561024 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561088 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 8884593 d127 d128
private def d122 : MobiusHarmonicTree := .branch 19314992 d123 d126
private def d114 : MobiusHarmonicTree := .branch 32398591 d115 d122
private def d98 : MobiusHarmonicTree := .branch 52819986 d99 d114
private def d66 : MobiusHarmonicTree := .branch 81615738 d67 d98
private def d2 : MobiusHarmonicTree := .branch 217839231 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561152 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561216 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 8328464 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561280 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561344 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 5542149 d138 d139
private def d133 : MobiusHarmonicTree := .branch 13870613 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561408 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561472 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 1236135 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561536 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561600 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 1091552 d145 d146
private def d140 : MobiusHarmonicTree := .branch 2327687 d141 d144
private def d132 : MobiusHarmonicTree := .branch 16198300 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561664 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561728 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 3588963 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561792 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561856 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 4170130 d153 d154
private def d148 : MobiusHarmonicTree := .branch 7759093 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561920 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 561984 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 4025121 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562048 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562112 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 5756901 d160 d161
private def d155 : MobiusHarmonicTree := .branch 9782022 d156 d159
private def d147 : MobiusHarmonicTree := .branch 17541115 d148 d155
private def d131 : MobiusHarmonicTree := .branch 33739415 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562176 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562240 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 6445754 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562304 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562368 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 5051936 d169 d170
private def d164 : MobiusHarmonicTree := .branch 11497690 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562432 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562496 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 6599175 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562560 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562624 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 6441378 d176 d177
private def d171 : MobiusHarmonicTree := .branch 13040553 d172 d175
private def d163 : MobiusHarmonicTree := .branch 24538243 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562688 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562752 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 4140455 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562816 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562880 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 4359783 d184 d185
private def d179 : MobiusHarmonicTree := .branch 8500238 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 562944 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563008 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 4911188 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563072 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563136 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 5753536 d191 d192
private def d186 : MobiusHarmonicTree := .branch 10664724 d187 d190
private def d178 : MobiusHarmonicTree := .branch 19164962 d179 d186
private def d162 : MobiusHarmonicTree := .branch 43703205 d163 d178
private def d130 : MobiusHarmonicTree := .branch 77442620 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563200 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563264 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 6061138 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563328 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563392 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 5364054 d201 d202
private def d196 : MobiusHarmonicTree := .branch 11425192 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563456 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563520 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 3561643 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563584 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563648 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 4474440 d208 d209
private def d203 : MobiusHarmonicTree := .branch 8036083 d204 d207
private def d195 : MobiusHarmonicTree := .branch 19461275 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563712 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563776 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 6522195 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563840 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563904 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 5164054 d216 d217
private def d211 : MobiusHarmonicTree := .branch 11686249 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 563968 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564032 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 4253411 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564096 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564160 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 2658893 d223 d224
private def d218 : MobiusHarmonicTree := .branch 6912304 d219 d222
private def d210 : MobiusHarmonicTree := .branch 18598553 d211 d218
private def d194 : MobiusHarmonicTree := .branch 38059828 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564224 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564288 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 1889232 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564352 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564416 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 2131411 d232 d233
private def d227 : MobiusHarmonicTree := .branch 4020643 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564480 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564544 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 1976941 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564608 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564672 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 1299888 d239 d240
private def d234 : MobiusHarmonicTree := .branch 3276829 d235 d238
private def d226 : MobiusHarmonicTree := .branch 7297472 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564736 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564800 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 1462557 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564864 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564928 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 892220 d247 d248
private def d242 : MobiusHarmonicTree := .branch 2354777 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 564992 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565056 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 1364484 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565120 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock068 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565184 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 2471762 d254 d255
private def d249 : MobiusHarmonicTree := .branch 3836246 d250 d253
private def d241 : MobiusHarmonicTree := .branch 6191023 d242 d249
private def d225 : MobiusHarmonicTree := .branch 13488495 d226 d241
private def d193 : MobiusHarmonicTree := .branch 51548323 d194 d225
private def d129 : MobiusHarmonicTree := .branch 128990943 d130 d193
private def d1 : MobiusHarmonicTree := .branch 346830174 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565248 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565312 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 2894047 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565376 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565440 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 1885342 d266 d267
private def d261 : MobiusHarmonicTree := .branch 4779389 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565504 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565568 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 1112202 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565632 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565696 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 477323 d273 d274
private def d268 : MobiusHarmonicTree := .branch 1589525 d269 d272
private def d260 : MobiusHarmonicTree := .branch 6368914 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565760 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565824 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 1436870 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565888 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 565952 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 2565662 d281 d282
private def d276 : MobiusHarmonicTree := .branch 4002532 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566016 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566080 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 3268156 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566144 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566208 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 3756636 d288 d289
private def d283 : MobiusHarmonicTree := .branch 7024792 d284 d287
private def d275 : MobiusHarmonicTree := .branch 11027324 d276 d283
private def d259 : MobiusHarmonicTree := .branch 17396238 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566272 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566336 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 5606241 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566400 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566464 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 6143462 d297 d298
private def d292 : MobiusHarmonicTree := .branch 11749703 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566528 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566592 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 6034404 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566656 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566720 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 3984463 d304 d305
private def d299 : MobiusHarmonicTree := .branch 10018867 d300 d303
private def d291 : MobiusHarmonicTree := .branch 21768570 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566784 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566848 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 3672970 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566912 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 566976 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 5053196 d312 d313
private def d307 : MobiusHarmonicTree := .branch 8726166 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567040 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567104 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 4983293 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567168 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567232 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 5870667 d319 d320
private def d314 : MobiusHarmonicTree := .branch 10853960 d315 d318
private def d306 : MobiusHarmonicTree := .branch 19580126 d307 d314
private def d290 : MobiusHarmonicTree := .branch 41348696 d291 d306
private def d258 : MobiusHarmonicTree := .branch 58744934 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567296 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567360 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 3988766 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567424 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567488 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 3159593 d329 d330
private def d324 : MobiusHarmonicTree := .branch 7148359 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567552 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567616 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 4686337 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567680 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567744 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 4288961 d336 d337
private def d331 : MobiusHarmonicTree := .branch 8975298 d332 d335
private def d323 : MobiusHarmonicTree := .branch 16123657 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567808 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567872 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 1558567 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 567936 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568000 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 1336331 d344 d345
private def d339 : MobiusHarmonicTree := .branch 2894898 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568064 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568128 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 2566350 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568192 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568256 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 3568913 d351 d352
private def d346 : MobiusHarmonicTree := .branch 6135263 d347 d350
private def d338 : MobiusHarmonicTree := .branch 9030161 d339 d346
private def d322 : MobiusHarmonicTree := .branch 25153818 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568320 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568384 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 1588826 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568448 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568512 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 1340371 d360 d361
private def d355 : MobiusHarmonicTree := .branch 2929197 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568576 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568640 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 3469716 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568704 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568768 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 2067669 d367 d368
private def d362 : MobiusHarmonicTree := .branch 5537385 d363 d366
private def d354 : MobiusHarmonicTree := .branch 8466582 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568832 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568896 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 4209976 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 568960 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569024 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 5136934 d375 d376
private def d370 : MobiusHarmonicTree := .branch 9346910 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569088 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569152 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 6297127 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569216 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569280 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 6511795 d382 d383
private def d377 : MobiusHarmonicTree := .branch 12808922 d378 d381
private def d369 : MobiusHarmonicTree := .branch 22155832 d370 d377
private def d353 : MobiusHarmonicTree := .branch 30622414 d354 d369
private def d321 : MobiusHarmonicTree := .branch 55776232 d322 d353
private def d257 : MobiusHarmonicTree := .branch 114521166 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569344 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569408 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 7878410 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569472 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569536 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 10833372 d393 d394
private def d388 : MobiusHarmonicTree := .branch 18711782 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569600 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569664 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 11269895 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569728 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569792 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 9698356 d400 d401
private def d395 : MobiusHarmonicTree := .branch 20968251 d396 d399
private def d387 : MobiusHarmonicTree := .branch 39680033 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569856 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569920 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 7531009 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 569984 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570048 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 4978656 d408 d409
private def d403 : MobiusHarmonicTree := .branch 12509665 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570112 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570176 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 2778160 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570240 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570304 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 5058736 d415 d416
private def d410 : MobiusHarmonicTree := .branch 7836896 d411 d414
private def d402 : MobiusHarmonicTree := .branch 20346561 d403 d410
private def d386 : MobiusHarmonicTree := .branch 60026594 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570368 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570432 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 4621152 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570496 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570560 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 1437274 d424 d425
private def d419 : MobiusHarmonicTree := .branch 6058426 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570624 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570688 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 1964326 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570752 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570816 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 2550826 d431 d432
private def d426 : MobiusHarmonicTree := .branch 4515152 d427 d430
private def d418 : MobiusHarmonicTree := .branch 10573578 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570880 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 570944 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 942379 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571008 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571072 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 514897 d439 d440
private def d434 : MobiusHarmonicTree := .branch 1457276 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571136 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571200 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 1104750 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571264 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571328 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 1174485 d446 d447
private def d441 : MobiusHarmonicTree := .branch 2279235 d442 d445
private def d433 : MobiusHarmonicTree := .branch 3736511 d434 d441
private def d417 : MobiusHarmonicTree := .branch 14310089 d418 d433
private def d385 : MobiusHarmonicTree := .branch 74336683 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571392 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571456 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 1637970 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571520 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571584 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 684118 d456 d457
private def d451 : MobiusHarmonicTree := .branch 2322088 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571648 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571712 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 568524 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571776 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571840 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 895418 d463 d464
private def d458 : MobiusHarmonicTree := .branch 1463942 d459 d462
private def d450 : MobiusHarmonicTree := .branch 3786030 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571904 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 571968 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 725616 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572032 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572096 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 1484072 d471 d472
private def d466 : MobiusHarmonicTree := .branch 2209688 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572160 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572224 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 767239 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572288 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572352 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 1714010 d478 d479
private def d473 : MobiusHarmonicTree := .branch 2481249 d474 d477
private def d465 : MobiusHarmonicTree := .branch 4690937 d466 d473
private def d449 : MobiusHarmonicTree := .branch 8476967 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572416 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572480 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 3778318 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572544 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572608 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 5518644 d487 d488
private def d482 : MobiusHarmonicTree := .branch 9296962 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572672 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572736 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 8304045 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572800 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572864 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 11494902 d494 d495
private def d489 : MobiusHarmonicTree := .branch 19798947 d490 d493
private def d481 : MobiusHarmonicTree := .branch 29095909 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572928 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 572992 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 12965344 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573056 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573120 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 11990637 d502 d503
private def d497 : MobiusHarmonicTree := .branch 24955981 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573184 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573248 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 9578897 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573312 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock069 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 573376 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 8343631 d509 d510
private def d504 : MobiusHarmonicTree := .branch 17922528 d505 d508
private def d496 : MobiusHarmonicTree := .branch 42878509 d497 d504
private def d480 : MobiusHarmonicTree := .branch 71974418 d481 d496
private def d448 : MobiusHarmonicTree := .branch 80451385 d449 d480
private def d384 : MobiusHarmonicTree := .branch 154788068 d385 d448
private def d256 : MobiusHarmonicTree := .branch 269309234 d257 d384
private def d0 : MobiusHarmonicTree := .branch 616139408 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 557056 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 557056 616139408 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 557056 346830174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 557056 217839231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 557056 136223493 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 557056 63372581 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 557056 20262288 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 557056 5269065 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 557056 1373140 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 557184 3895925 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 557312 14993223 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 557312 5911634 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 557440 9081589 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 557568 43110293 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 557568 20717459 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 557568 10063999 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 557696 10653460 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 557824 22392834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 557824 11570489 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 557952 10822345 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 558080 72850912 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 558080 44378861 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 558080 22079881 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 558080 11583093 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 558208 10496788 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 558336 22298980 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 558336 11694169 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 558464 10604811 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 558592 28472051 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 558592 15643156 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 558592 8237693 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 558720 7405463 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 558848 12828895 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 558848 6187072 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 558976 6641823 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 559104 81615738 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 559104 28795752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 559104 23266423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 559104 15136941 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 559104 7614911 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 559232 7522030 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 559360 8129482 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 559360 5816795 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 559488 2312687 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 559616 5529329 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 559616 1218548 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 559616 616506 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 559744 602042 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 559872 4310781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 559872 2093130 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 560000 2217651 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 560128 52819986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 560128 20421395 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 560128 9713261 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 560128 3993259 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 560256 5720002 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 560384 10708134 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 560384 5233355 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 560512 5474779 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 560640 32398591 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 560640 13083599 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 560640 5243481 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 560768 7840118 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 560896 19314992 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 560896 10430399 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 561024 8884593 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 561152 128990943 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 561152 77442620 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 561152 33739415 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 561152 16198300 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 561152 13870613 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 561152 8328464 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 561280 5542149 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 561408 2327687 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 561408 1236135 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 561536 1091552 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 561664 17541115 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 561664 7759093 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 561664 3588963 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 561792 4170130 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 561920 9782022 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 561920 4025121 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 562048 5756901 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 562176 43703205 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 562176 24538243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 562176 11497690 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 562176 6445754 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 562304 5051936 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 562432 13040553 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 562432 6599175 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 562560 6441378 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 562688 19164962 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 562688 8500238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 562688 4140455 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 562816 4359783 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 562944 10664724 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 562944 4911188 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 563072 5753536 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 563200 51548323 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 563200 38059828 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 563200 19461275 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 563200 11425192 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 563200 6061138 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 563328 5364054 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 563456 8036083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 563456 3561643 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 563584 4474440 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 563712 18598553 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 563712 11686249 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 563712 6522195 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 563840 5164054 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 563968 6912304 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 563968 4253411 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 564096 2658893 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 564224 13488495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 564224 7297472 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 564224 4020643 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 564224 1889232 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 564352 2131411 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 564480 3276829 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 564480 1976941 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 564608 1299888 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 564736 6191023 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 564736 2354777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 564736 1462557 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 564864 892220 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 564992 3836246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 564992 1364484 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 565120 2471762 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 565248 269309234 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 565248 114521166 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 565248 58744934 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 565248 17396238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 565248 6368914 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 565248 4779389 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 565248 2894047 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 565376 1885342 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 565504 1589525 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 565504 1112202 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 565632 477323 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 565760 11027324 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 565760 4002532 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 565760 1436870 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 565888 2565662 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 566016 7024792 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 566016 3268156 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 566144 3756636 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 566272 41348696 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 566272 21768570 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 566272 11749703 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 566272 5606241 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 566400 6143462 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 566528 10018867 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 566528 6034404 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 566656 3984463 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 566784 19580126 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 566784 8726166 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 566784 3672970 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 566912 5053196 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 567040 10853960 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 567040 4983293 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 567168 5870667 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 567296 55776232 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 567296 25153818 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 567296 16123657 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 567296 7148359 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 567296 3988766 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 567424 3159593 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 567552 8975298 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 567552 4686337 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 567680 4288961 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 567808 9030161 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 567808 2894898 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 567808 1558567 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 567936 1336331 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 568064 6135263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 568064 2566350 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 568192 3568913 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 568320 30622414 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 568320 8466582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 568320 2929197 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 568320 1588826 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 568448 1340371 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 568576 5537385 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 568576 3469716 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 568704 2067669 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 568832 22155832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 568832 9346910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 568832 4209976 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 568960 5136934 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 569088 12808922 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 569088 6297127 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 569216 6511795 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 569344 154788068 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 569344 74336683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 569344 60026594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 569344 39680033 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 569344 18711782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 569344 7878410 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 569472 10833372 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 569600 20968251 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 569600 11269895 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 569728 9698356 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 569856 20346561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 569856 12509665 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 569856 7531009 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 569984 4978656 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 570112 7836896 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 570112 2778160 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 570240 5058736 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 570368 14310089 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 570368 10573578 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 570368 6058426 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 570368 4621152 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 570496 1437274 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 570624 4515152 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 570624 1964326 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 570752 2550826 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 570880 3736511 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 570880 1457276 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 570880 942379 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 571008 514897 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 571136 2279235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 571136 1104750 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 571264 1174485 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 571392 80451385 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 571392 8476967 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 571392 3786030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 571392 2322088 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 571392 1637970 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 571520 684118 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 571648 1463942 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 571648 568524 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 571776 895418 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 571904 4690937 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 571904 2209688 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 571904 725616 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 572032 1484072 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 572160 2481249 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 572160 767239 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 572288 1714010 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 572416 71974418 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 572416 29095909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 572416 9296962 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 572416 3778318 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 572544 5518644 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 572672 19798947 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 572672 8304045 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 572800 11494902 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 572928 42878509 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 572928 24955981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 572928 12965344 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 573056 11990637 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 573184 17922528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 573184 9578897 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 573312 8343631 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 557056 (MobiusHarmonicTree.branch 616139408 mobiusHarmonicBlock068 mobiusHarmonicBlock069) = true := Helfgott.combined

#print axioms solution
