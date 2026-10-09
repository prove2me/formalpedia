-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair062_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:44:29.130503+00:00
-- url     : https://prove2.me/submissions/7647acff-488d-49f0-a038-95c1d6725edc

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015808 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015872 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 21006677 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015936 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016000 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 19478429 d11 d12
private def d6 : MobiusHarmonicTree := .branch 40485106 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016064 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016128 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 17394549 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016192 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016256 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 17404138 d18 d19
private def d13 : MobiusHarmonicTree := .branch 34798687 d14 d17
private def d5 : MobiusHarmonicTree := .branch 75283793 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016320 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016384 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 18289416 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016448 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016512 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 19169536 d26 d27
private def d21 : MobiusHarmonicTree := .branch 37458952 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016576 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016640 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 19267472 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016704 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016768 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 19438139 d33 d34
private def d28 : MobiusHarmonicTree := .branch 38705611 d29 d32
private def d20 : MobiusHarmonicTree := .branch 76164563 d21 d28
private def d4 : MobiusHarmonicTree := .branch 151448356 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016832 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016896 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 19123965 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1016960 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017024 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 18603369 d42 d43
private def d37 : MobiusHarmonicTree := .branch 37727334 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017088 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017152 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 18621679 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017216 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017280 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 17817188 d49 d50
private def d44 : MobiusHarmonicTree := .branch 36438867 d45 d48
private def d36 : MobiusHarmonicTree := .branch 74166201 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017344 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017408 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 17982036 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017472 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017536 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 17300703 d57 d58
private def d52 : MobiusHarmonicTree := .branch 35282739 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017600 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017664 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 16756100 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017728 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017792 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 16328562 d64 d65
private def d59 : MobiusHarmonicTree := .branch 33084662 d60 d63
private def d51 : MobiusHarmonicTree := .branch 68367401 d52 d59
private def d35 : MobiusHarmonicTree := .branch 142533602 d36 d51
private def d3 : MobiusHarmonicTree := .branch 293981958 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017856 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017920 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 16815714 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1017984 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018048 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 16850948 d74 d75
private def d69 : MobiusHarmonicTree := .branch 33666662 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018112 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018176 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 17015793 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018240 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018304 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 17983870 d81 d82
private def d76 : MobiusHarmonicTree := .branch 34999663 d77 d80
private def d68 : MobiusHarmonicTree := .branch 68666325 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018368 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018432 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 17945323 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018496 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018560 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 18067714 d89 d90
private def d84 : MobiusHarmonicTree := .branch 36013037 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018624 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018688 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 17124092 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018752 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018816 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 16053019 d96 d97
private def d91 : MobiusHarmonicTree := .branch 33177111 d92 d95
private def d83 : MobiusHarmonicTree := .branch 69190148 d84 d91
private def d67 : MobiusHarmonicTree := .branch 137856473 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018880 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1018944 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 15448448 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019008 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019072 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 14253234 d105 d106
private def d100 : MobiusHarmonicTree := .branch 29701682 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019136 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019200 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 14905879 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019264 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019328 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 15230698 d112 d113
private def d107 : MobiusHarmonicTree := .branch 30136577 d108 d111
private def d99 : MobiusHarmonicTree := .branch 59838259 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019392 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019456 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 14538223 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019520 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019584 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 14847301 d120 d121
private def d115 : MobiusHarmonicTree := .branch 29385524 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019648 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019712 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 12950809 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019776 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019840 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 11369522 d127 d128
private def d122 : MobiusHarmonicTree := .branch 24320331 d123 d126
private def d114 : MobiusHarmonicTree := .branch 53705855 d115 d122
private def d98 : MobiusHarmonicTree := .branch 113544114 d99 d114
private def d66 : MobiusHarmonicTree := .branch 251400587 d67 d98
private def d2 : MobiusHarmonicTree := .branch 545382545 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019904 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1019968 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 11292570 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020032 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020096 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 10713769 d138 d139
private def d133 : MobiusHarmonicTree := .branch 22006339 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020160 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020224 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 11323065 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020288 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020352 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 11321661 d145 d146
private def d140 : MobiusHarmonicTree := .branch 22644726 d141 d144
private def d132 : MobiusHarmonicTree := .branch 44651065 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020416 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020480 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 11677901 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020544 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020608 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 12277055 d153 d154
private def d148 : MobiusHarmonicTree := .branch 23954956 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020672 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020736 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 12823163 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020800 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020864 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 12465013 d160 d161
private def d155 : MobiusHarmonicTree := .branch 25288176 d156 d159
private def d147 : MobiusHarmonicTree := .branch 49243132 d148 d155
private def d131 : MobiusHarmonicTree := .branch 93894197 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020928 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1020992 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 12098116 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021056 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021120 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 10327955 d169 d170
private def d164 : MobiusHarmonicTree := .branch 22426071 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021184 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021248 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 10378552 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021312 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021376 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 8333940 d176 d177
private def d171 : MobiusHarmonicTree := .branch 18712492 d172 d175
private def d163 : MobiusHarmonicTree := .branch 41138563 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021440 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021504 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 7432243 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021568 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021632 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 6671761 d184 d185
private def d179 : MobiusHarmonicTree := .branch 14104004 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021696 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021760 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 6252018 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021824 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021888 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 7175994 d191 d192
private def d186 : MobiusHarmonicTree := .branch 13428012 d187 d190
private def d178 : MobiusHarmonicTree := .branch 27532016 d179 d186
private def d162 : MobiusHarmonicTree := .branch 68670579 d163 d178
private def d130 : MobiusHarmonicTree := .branch 162564776 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1021952 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022016 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 7125198 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022080 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022144 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 7530331 d201 d202
private def d196 : MobiusHarmonicTree := .branch 14655529 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022208 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022272 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 6120760 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022336 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022400 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 6732250 d208 d209
private def d203 : MobiusHarmonicTree := .branch 12853010 d204 d207
private def d195 : MobiusHarmonicTree := .branch 27508539 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022464 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022528 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 8218905 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022592 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022656 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 8206170 d216 d217
private def d211 : MobiusHarmonicTree := .branch 16425075 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022720 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022784 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 8740892 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022848 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022912 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 9893385 d223 d224
private def d218 : MobiusHarmonicTree := .branch 18634277 d219 d222
private def d210 : MobiusHarmonicTree := .branch 35059352 d211 d218
private def d194 : MobiusHarmonicTree := .branch 62567891 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1022976 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023040 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 9937124 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023104 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023168 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 9461867 d232 d233
private def d227 : MobiusHarmonicTree := .branch 19398991 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023232 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023296 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 7053767 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023360 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023424 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 5754273 d239 d240
private def d234 : MobiusHarmonicTree := .branch 12808040 d235 d238
private def d226 : MobiusHarmonicTree := .branch 32207031 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023488 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023552 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 5007158 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023616 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023680 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 4376420 d247 d248
private def d242 : MobiusHarmonicTree := .branch 9383578 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023744 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023808 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 5743322 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023872 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock124 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1023936 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 6921385 d254 d255
private def d249 : MobiusHarmonicTree := .branch 12664707 d250 d253
private def d241 : MobiusHarmonicTree := .branch 22048285 d242 d249
private def d225 : MobiusHarmonicTree := .branch 54255316 d226 d241
private def d193 : MobiusHarmonicTree := .branch 116823207 d194 d225
private def d129 : MobiusHarmonicTree := .branch 279387983 d130 d193
private def d1 : MobiusHarmonicTree := .branch 824770528 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024000 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024064 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 8277872 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024128 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024192 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 7162791 d266 d267
private def d261 : MobiusHarmonicTree := .branch 15440663 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024256 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024320 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 7654897 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024384 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024448 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 7711543 d273 d274
private def d268 : MobiusHarmonicTree := .branch 15366440 d269 d272
private def d260 : MobiusHarmonicTree := .branch 30807103 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024512 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024576 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 8153675 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024640 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024704 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 9143191 d281 d282
private def d276 : MobiusHarmonicTree := .branch 17296866 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024768 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024832 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 9159621 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024896 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024960 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 8519436 d288 d289
private def d283 : MobiusHarmonicTree := .branch 17679057 d284 d287
private def d275 : MobiusHarmonicTree := .branch 34975923 d276 d283
private def d259 : MobiusHarmonicTree := .branch 65783026 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025024 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025088 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 6935092 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025152 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025216 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 7115633 d297 d298
private def d292 : MobiusHarmonicTree := .branch 14050725 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025280 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025344 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 6727552 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025408 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025472 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 6558986 d304 d305
private def d299 : MobiusHarmonicTree := .branch 13286538 d300 d303
private def d291 : MobiusHarmonicTree := .branch 27337263 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025536 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025600 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 7058367 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025664 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025728 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 8340482 d312 d313
private def d307 : MobiusHarmonicTree := .branch 15398849 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025792 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025856 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 8942828 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025920 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1025984 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 8837440 d319 d320
private def d314 : MobiusHarmonicTree := .branch 17780268 d315 d318
private def d306 : MobiusHarmonicTree := .branch 33179117 d307 d314
private def d290 : MobiusHarmonicTree := .branch 60516380 d291 d306
private def d258 : MobiusHarmonicTree := .branch 126299406 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026048 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026112 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 8377321 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026176 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026240 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 8260314 d329 d330
private def d324 : MobiusHarmonicTree := .branch 16637635 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026304 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026368 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 8116072 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026432 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026496 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 6724882 d336 d337
private def d331 : MobiusHarmonicTree := .branch 14840954 d332 d335
private def d323 : MobiusHarmonicTree := .branch 31478589 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026560 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026624 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 7957198 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026688 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026752 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 9844700 d344 d345
private def d339 : MobiusHarmonicTree := .branch 17801898 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026816 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026880 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 10370303 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1026944 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027008 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 9712755 d351 d352
private def d346 : MobiusHarmonicTree := .branch 20083058 d347 d350
private def d338 : MobiusHarmonicTree := .branch 37884956 d339 d346
private def d322 : MobiusHarmonicTree := .branch 69363545 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027072 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027136 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 10231424 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027200 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027264 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 10011129 d360 d361
private def d355 : MobiusHarmonicTree := .branch 20242553 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027328 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027392 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 10477071 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027456 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027520 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 10696697 d367 d368
private def d362 : MobiusHarmonicTree := .branch 21173768 d363 d366
private def d354 : MobiusHarmonicTree := .branch 41416321 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027584 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027648 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 11142012 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027712 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027776 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 12285808 d375 d376
private def d370 : MobiusHarmonicTree := .branch 23427820 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027840 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027904 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 12577111 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1027968 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028032 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 14066743 d382 d383
private def d377 : MobiusHarmonicTree := .branch 26643854 d378 d381
private def d369 : MobiusHarmonicTree := .branch 50071674 d370 d377
private def d353 : MobiusHarmonicTree := .branch 91487995 d354 d369
private def d321 : MobiusHarmonicTree := .branch 160851540 d322 d353
private def d257 : MobiusHarmonicTree := .branch 287150946 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028096 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028160 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 12893991 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028224 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028288 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 12347784 d393 d394
private def d388 : MobiusHarmonicTree := .branch 25241775 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028352 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028416 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 12418195 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028480 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028544 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 12349556 d400 d401
private def d395 : MobiusHarmonicTree := .branch 24767751 d396 d399
private def d387 : MobiusHarmonicTree := .branch 50009526 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028608 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028672 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 11958239 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028736 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028800 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 10162405 d408 d409
private def d403 : MobiusHarmonicTree := .branch 22120644 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028864 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028928 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 9572171 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1028992 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029056 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 9733246 d415 d416
private def d410 : MobiusHarmonicTree := .branch 19305417 d411 d414
private def d402 : MobiusHarmonicTree := .branch 41426061 d403 d410
private def d386 : MobiusHarmonicTree := .branch 91435587 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029120 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029184 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 9178227 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029248 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029312 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 8475645 d424 d425
private def d419 : MobiusHarmonicTree := .branch 17653872 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029376 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029440 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 7451683 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029504 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029568 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 6834000 d431 d432
private def d426 : MobiusHarmonicTree := .branch 14285683 d427 d430
private def d418 : MobiusHarmonicTree := .branch 31939555 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029632 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029696 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 8079127 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029760 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029824 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 8652047 d439 d440
private def d434 : MobiusHarmonicTree := .branch 16731174 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029888 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1029952 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 6953800 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030016 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030080 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 4623008 d446 d447
private def d441 : MobiusHarmonicTree := .branch 11576808 d442 d445
private def d433 : MobiusHarmonicTree := .branch 28307982 d434 d441
private def d417 : MobiusHarmonicTree := .branch 60247537 d418 d433
private def d385 : MobiusHarmonicTree := .branch 151683124 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030144 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030208 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 4574878 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030272 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030336 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 4010402 d456 d457
private def d451 : MobiusHarmonicTree := .branch 8585280 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030400 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030464 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 4174887 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030528 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030592 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 4856477 d463 d464
private def d458 : MobiusHarmonicTree := .branch 9031364 d459 d462
private def d450 : MobiusHarmonicTree := .branch 17616644 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030656 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030720 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 5873620 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030784 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030848 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 5499422 d471 d472
private def d466 : MobiusHarmonicTree := .branch 11373042 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030912 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1030976 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 5581197 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031040 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031104 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 6626931 d478 d479
private def d473 : MobiusHarmonicTree := .branch 12208128 d474 d477
private def d465 : MobiusHarmonicTree := .branch 23581170 d466 d473
private def d449 : MobiusHarmonicTree := .branch 41197814 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031168 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031232 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 7763591 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031296 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031360 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 9576719 d487 d488
private def d482 : MobiusHarmonicTree := .branch 17340310 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031424 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031488 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 10441304 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031552 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031616 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 9745952 d494 d495
private def d489 : MobiusHarmonicTree := .branch 20187256 d490 d493
private def d481 : MobiusHarmonicTree := .branch 37527566 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031680 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031744 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 10236138 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031808 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031872 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 10426729 d502 d503
private def d497 : MobiusHarmonicTree := .branch 20662867 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1031936 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032000 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 11494251 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032064 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock125 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032128 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 11624591 d509 d510
private def d504 : MobiusHarmonicTree := .branch 23118842 d505 d508
private def d496 : MobiusHarmonicTree := .branch 43781709 d497 d504
private def d480 : MobiusHarmonicTree := .branch 81309275 d481 d496
private def d448 : MobiusHarmonicTree := .branch 122507089 d449 d480
private def d384 : MobiusHarmonicTree := .branch 274190213 d385 d448
private def d256 : MobiusHarmonicTree := .branch 561341159 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1386111687 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 1015808 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 1015808 1386111687 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 1015808 824770528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1015808 545382545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1015808 293981958 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1015808 151448356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1015808 75283793 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1015808 40485106 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1015808 21006677 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1015936 19478429 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1016064 34798687 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1016064 17394549 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1016192 17404138 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1016320 76164563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1016320 37458952 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1016320 18289416 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1016448 19169536 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1016576 38705611 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1016576 19267472 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1016704 19438139 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1016832 142533602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1016832 74166201 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1016832 37727334 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1016832 19123965 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1016960 18603369 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1017088 36438867 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1017088 18621679 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1017216 17817188 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1017344 68367401 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1017344 35282739 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1017344 17982036 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1017472 17300703 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1017600 33084662 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1017600 16756100 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1017728 16328562 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1017856 251400587 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1017856 137856473 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1017856 68666325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1017856 33666662 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1017856 16815714 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1017984 16850948 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1018112 34999663 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1018112 17015793 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1018240 17983870 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1018368 69190148 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1018368 36013037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1018368 17945323 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1018496 18067714 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1018624 33177111 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1018624 17124092 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1018752 16053019 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1018880 113544114 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1018880 59838259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1018880 29701682 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1018880 15448448 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1019008 14253234 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1019136 30136577 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1019136 14905879 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1019264 15230698 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1019392 53705855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1019392 29385524 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1019392 14538223 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1019520 14847301 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1019648 24320331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1019648 12950809 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1019776 11369522 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1019904 279387983 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1019904 162564776 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1019904 93894197 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1019904 44651065 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1019904 22006339 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1019904 11292570 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1020032 10713769 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1020160 22644726 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1020160 11323065 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1020288 11321661 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1020416 49243132 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1020416 23954956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1020416 11677901 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1020544 12277055 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1020672 25288176 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1020672 12823163 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1020800 12465013 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1020928 68670579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1020928 41138563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1020928 22426071 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1020928 12098116 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1021056 10327955 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1021184 18712492 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1021184 10378552 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1021312 8333940 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1021440 27532016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1021440 14104004 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1021440 7432243 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1021568 6671761 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1021696 13428012 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1021696 6252018 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1021824 7175994 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1021952 116823207 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1021952 62567891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1021952 27508539 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1021952 14655529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1021952 7125198 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1022080 7530331 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1022208 12853010 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1022208 6120760 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1022336 6732250 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1022464 35059352 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1022464 16425075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1022464 8218905 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1022592 8206170 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1022720 18634277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1022720 8740892 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1022848 9893385 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1022976 54255316 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1022976 32207031 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1022976 19398991 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1022976 9937124 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1023104 9461867 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1023232 12808040 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1023232 7053767 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1023360 5754273 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1023488 22048285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1023488 9383578 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1023488 5007158 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1023616 4376420 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1023744 12664707 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1023744 5743322 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1023872 6921385 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 1024000 561341159 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1024000 287150946 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1024000 126299406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1024000 65783026 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1024000 30807103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1024000 15440663 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1024000 8277872 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1024128 7162791 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1024256 15366440 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1024256 7654897 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1024384 7711543 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1024512 34975923 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1024512 17296866 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1024512 8153675 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1024640 9143191 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1024768 17679057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1024768 9159621 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1024896 8519436 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1025024 60516380 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1025024 27337263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1025024 14050725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1025024 6935092 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1025152 7115633 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1025280 13286538 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1025280 6727552 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1025408 6558986 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1025536 33179117 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1025536 15398849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1025536 7058367 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1025664 8340482 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1025792 17780268 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1025792 8942828 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1025920 8837440 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1026048 160851540 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1026048 69363545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1026048 31478589 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1026048 16637635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1026048 8377321 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1026176 8260314 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1026304 14840954 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1026304 8116072 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1026432 6724882 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1026560 37884956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1026560 17801898 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1026560 7957198 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1026688 9844700 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1026816 20083058 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1026816 10370303 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1026944 9712755 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1027072 91487995 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1027072 41416321 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1027072 20242553 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1027072 10231424 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1027200 10011129 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1027328 21173768 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1027328 10477071 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1027456 10696697 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1027584 50071674 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1027584 23427820 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1027584 11142012 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1027712 12285808 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1027840 26643854 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1027840 12577111 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1027968 14066743 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1028096 274190213 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1028096 151683124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1028096 91435587 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1028096 50009526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1028096 25241775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1028096 12893991 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1028224 12347784 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1028352 24767751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1028352 12418195 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1028480 12349556 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1028608 41426061 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1028608 22120644 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1028608 11958239 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1028736 10162405 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1028864 19305417 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1028864 9572171 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1028992 9733246 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1029120 60247537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1029120 31939555 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1029120 17653872 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1029120 9178227 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1029248 8475645 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1029376 14285683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1029376 7451683 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1029504 6834000 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1029632 28307982 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1029632 16731174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1029632 8079127 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1029760 8652047 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1029888 11576808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1029888 6953800 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1030016 4623008 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1030144 122507089 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1030144 41197814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1030144 17616644 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1030144 8585280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1030144 4574878 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1030272 4010402 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1030400 9031364 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1030400 4174887 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1030528 4856477 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1030656 23581170 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1030656 11373042 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1030656 5873620 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1030784 5499422 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1030912 12208128 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1030912 5581197 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1031040 6626931 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1031168 81309275 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1031168 37527566 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1031168 17340310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1031168 7763591 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1031296 9576719 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1031424 20187256 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1031424 10441304 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1031552 9745952 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1031680 43781709 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1031680 20662867 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1031680 10236138 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1031808 10426729 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1031936 23118842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1031936 11494251 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1032064 11624591 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 1015808 (MobiusHarmonicTree.branch 1386111687 mobiusHarmonicBlock124 mobiusHarmonicBlock125) = true := Helfgott.combined

#print axioms solution
