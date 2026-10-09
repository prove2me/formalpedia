-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair027_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:35:10.370376+00:00
-- url     : https://prove2.me/submissions/82ee91e9-fb88-44d3-9513-4f5d3dd91286

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442368 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442432 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 6374005 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442496 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442560 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 6735828 d11 d12
private def d6 : MobiusHarmonicTree := .branch 13109833 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442624 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442688 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 5285960 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442752 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442816 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 7100039 d18 d19
private def d13 : MobiusHarmonicTree := .branch 12385999 d14 d17
private def d5 : MobiusHarmonicTree := .branch 25495832 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442880 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 442944 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 6438864 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443008 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443072 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 6775454 d26 d27
private def d21 : MobiusHarmonicTree := .branch 13214318 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443136 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443200 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 9020722 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443264 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443328 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 11156714 d33 d34
private def d28 : MobiusHarmonicTree := .branch 20177436 d29 d32
private def d20 : MobiusHarmonicTree := .branch 33391754 d21 d28
private def d4 : MobiusHarmonicTree := .branch 58887586 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443392 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443456 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 9108180 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443520 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443584 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 10563868 d42 d43
private def d37 : MobiusHarmonicTree := .branch 19672048 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443648 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443712 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 13628216 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443776 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443840 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 15181154 d49 d50
private def d44 : MobiusHarmonicTree := .branch 28809370 d45 d48
private def d36 : MobiusHarmonicTree := .branch 48481418 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443904 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 443968 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 14814278 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444032 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444096 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 13010785 d57 d58
private def d52 : MobiusHarmonicTree := .branch 27825063 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444160 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444224 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 13903083 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444288 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444352 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 11576593 d64 d65
private def d59 : MobiusHarmonicTree := .branch 25479676 d60 d63
private def d51 : MobiusHarmonicTree := .branch 53304739 d52 d59
private def d35 : MobiusHarmonicTree := .branch 101786157 d36 d51
private def d3 : MobiusHarmonicTree := .branch 160673743 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444416 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444480 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 11717031 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444544 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444608 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 13137559 d74 d75
private def d69 : MobiusHarmonicTree := .branch 24854590 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444672 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444736 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 8933581 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444800 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444864 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 10942598 d81 d82
private def d76 : MobiusHarmonicTree := .branch 19876179 d77 d80
private def d68 : MobiusHarmonicTree := .branch 44730769 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444928 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 444992 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 14281171 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445056 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445120 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 16276543 d89 d90
private def d84 : MobiusHarmonicTree := .branch 30557714 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445184 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445248 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 15959817 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445312 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445376 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 12383040 d96 d97
private def d91 : MobiusHarmonicTree := .branch 28342857 d92 d95
private def d83 : MobiusHarmonicTree := .branch 58900571 d84 d91
private def d67 : MobiusHarmonicTree := .branch 103631340 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445440 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445504 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 11070622 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445568 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445632 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 10383118 d105 d106
private def d100 : MobiusHarmonicTree := .branch 21453740 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445696 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445760 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 9478183 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445824 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445888 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 10489244 d112 d113
private def d107 : MobiusHarmonicTree := .branch 19967427 d108 d111
private def d99 : MobiusHarmonicTree := .branch 41421167 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 445952 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446016 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 9475214 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446080 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446144 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 6137131 d120 d121
private def d115 : MobiusHarmonicTree := .branch 15612345 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446208 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446272 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 5893272 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446336 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446400 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 5584784 d127 d128
private def d122 : MobiusHarmonicTree := .branch 11478056 d123 d126
private def d114 : MobiusHarmonicTree := .branch 27090401 d115 d122
private def d98 : MobiusHarmonicTree := .branch 68511568 d99 d114
private def d66 : MobiusHarmonicTree := .branch 172142908 d67 d98
private def d2 : MobiusHarmonicTree := .branch 332816651 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446464 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446528 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 3166835 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446592 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446656 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 2673137 d138 d139
private def d133 : MobiusHarmonicTree := .branch 5839972 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446720 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446784 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 3216405 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446848 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446912 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 3750300 d145 d146
private def d140 : MobiusHarmonicTree := .branch 6966705 d141 d144
private def d132 : MobiusHarmonicTree := .branch 12806677 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 446976 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447040 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 2867815 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447104 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447168 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 3727970 d153 d154
private def d148 : MobiusHarmonicTree := .branch 6595785 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447232 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447296 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 4616653 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447360 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447424 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 5344047 d160 d161
private def d155 : MobiusHarmonicTree := .branch 9960700 d156 d159
private def d147 : MobiusHarmonicTree := .branch 16556485 d148 d155
private def d131 : MobiusHarmonicTree := .branch 29363162 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447488 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447552 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 6032850 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447616 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447680 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 8582002 d169 d170
private def d164 : MobiusHarmonicTree := .branch 14614852 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447744 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447808 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 10227606 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447872 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 447936 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 10023856 d176 d177
private def d171 : MobiusHarmonicTree := .branch 20251462 d172 d175
private def d163 : MobiusHarmonicTree := .branch 34866314 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448000 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448064 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 10107971 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448128 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448192 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 9777264 d184 d185
private def d179 : MobiusHarmonicTree := .branch 19885235 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448256 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448320 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 11038969 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448384 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448448 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 15649411 d191 d192
private def d186 : MobiusHarmonicTree := .branch 26688380 d187 d190
private def d178 : MobiusHarmonicTree := .branch 46573615 d179 d186
private def d162 : MobiusHarmonicTree := .branch 81439929 d163 d178
private def d130 : MobiusHarmonicTree := .branch 110803091 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448512 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448576 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 20424645 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448640 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448704 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 21009536 d201 d202
private def d196 : MobiusHarmonicTree := .branch 41434181 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448768 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448832 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 20348436 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448896 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448960 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 19001875 d208 d209
private def d203 : MobiusHarmonicTree := .branch 39350311 d204 d207
private def d195 : MobiusHarmonicTree := .branch 80784492 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449024 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449088 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 19049770 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449152 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449216 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 18521267 d216 d217
private def d211 : MobiusHarmonicTree := .branch 37571037 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449280 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449344 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 17347649 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449408 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449472 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 15633893 d223 d224
private def d218 : MobiusHarmonicTree := .branch 32981542 d219 d222
private def d210 : MobiusHarmonicTree := .branch 70552579 d211 d218
private def d194 : MobiusHarmonicTree := .branch 151337071 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449536 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449600 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 14904521 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449664 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449728 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 12025162 d232 d233
private def d227 : MobiusHarmonicTree := .branch 26929683 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449792 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449856 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 13228657 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449920 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 449984 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 15236220 d239 d240
private def d234 : MobiusHarmonicTree := .branch 28464877 d235 d238
private def d226 : MobiusHarmonicTree := .branch 55394560 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450048 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450112 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 13163534 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450176 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450240 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 10194679 d247 d248
private def d242 : MobiusHarmonicTree := .branch 23358213 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450304 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450368 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 11259713 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450432 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock054 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450496 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 13569595 d254 d255
private def d249 : MobiusHarmonicTree := .branch 24829308 d250 d253
private def d241 : MobiusHarmonicTree := .branch 48187521 d242 d249
private def d225 : MobiusHarmonicTree := .branch 103582081 d226 d241
private def d193 : MobiusHarmonicTree := .branch 254919152 d194 d225
private def d129 : MobiusHarmonicTree := .branch 365722243 d130 d193
private def d1 : MobiusHarmonicTree := .branch 698538894 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450560 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450624 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 11260044 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450688 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450752 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 12911780 d266 d267
private def d261 : MobiusHarmonicTree := .branch 24171824 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450816 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450880 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 10047150 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 450944 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451008 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 11285878 d273 d274
private def d268 : MobiusHarmonicTree := .branch 21333028 d269 d272
private def d260 : MobiusHarmonicTree := .branch 45504852 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451072 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451136 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 11087606 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451200 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451264 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 14419549 d281 d282
private def d276 : MobiusHarmonicTree := .branch 25507155 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451328 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451392 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 10862042 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451456 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451520 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 11970782 d288 d289
private def d283 : MobiusHarmonicTree := .branch 22832824 d284 d287
private def d275 : MobiusHarmonicTree := .branch 48339979 d276 d283
private def d259 : MobiusHarmonicTree := .branch 93844831 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451584 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451648 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 9786560 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451712 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451776 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 6649455 d297 d298
private def d292 : MobiusHarmonicTree := .branch 16436015 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451840 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451904 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 5634033 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 451968 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452032 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 4059525 d304 d305
private def d299 : MobiusHarmonicTree := .branch 9693558 d300 d303
private def d291 : MobiusHarmonicTree := .branch 26129573 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452096 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452160 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 2419595 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452224 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452288 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 1370872 d312 d313
private def d307 : MobiusHarmonicTree := .branch 3790467 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452352 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452416 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 3983111 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452480 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452544 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 4879192 d319 d320
private def d314 : MobiusHarmonicTree := .branch 8862303 d315 d318
private def d306 : MobiusHarmonicTree := .branch 12652770 d307 d314
private def d290 : MobiusHarmonicTree := .branch 38782343 d291 d306
private def d258 : MobiusHarmonicTree := .branch 132627174 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452608 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452672 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 5323973 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452736 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452800 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 8191302 d329 d330
private def d324 : MobiusHarmonicTree := .branch 13515275 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452864 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452928 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 7617169 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 452992 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453056 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 10257101 d336 d337
private def d331 : MobiusHarmonicTree := .branch 17874270 d332 d335
private def d323 : MobiusHarmonicTree := .branch 31389545 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453120 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453184 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 7213562 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453248 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453312 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 5523918 d344 d345
private def d339 : MobiusHarmonicTree := .branch 12737480 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453376 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453440 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 3376427 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453504 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453568 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 8585254 d351 d352
private def d346 : MobiusHarmonicTree := .branch 11961681 d347 d350
private def d338 : MobiusHarmonicTree := .branch 24699161 d339 d346
private def d322 : MobiusHarmonicTree := .branch 56088706 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453632 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453696 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 10447592 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453760 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453824 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 10953635 d360 d361
private def d355 : MobiusHarmonicTree := .branch 21401227 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453888 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 453952 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 9677326 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454016 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454080 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 7494447 d367 d368
private def d362 : MobiusHarmonicTree := .branch 17171773 d363 d366
private def d354 : MobiusHarmonicTree := .branch 38573000 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454144 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454208 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 8322157 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454272 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454336 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 11418903 d375 d376
private def d370 : MobiusHarmonicTree := .branch 19741060 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454400 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454464 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 11393634 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454528 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454592 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 12732412 d382 d383
private def d377 : MobiusHarmonicTree := .branch 24126046 d378 d381
private def d369 : MobiusHarmonicTree := .branch 43867106 d370 d377
private def d353 : MobiusHarmonicTree := .branch 82440106 d354 d369
private def d321 : MobiusHarmonicTree := .branch 138528812 d322 d353
private def d257 : MobiusHarmonicTree := .branch 271155986 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454656 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454720 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 11840342 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454784 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454848 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 11808440 d393 d394
private def d388 : MobiusHarmonicTree := .branch 23648782 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454912 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 454976 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 9978662 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455040 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455104 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 12364225 d400 d401
private def d395 : MobiusHarmonicTree := .branch 22342887 d396 d399
private def d387 : MobiusHarmonicTree := .branch 45991669 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455168 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455232 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 15343879 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455296 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455360 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 15497717 d408 d409
private def d403 : MobiusHarmonicTree := .branch 30841596 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455424 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455488 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 14378178 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455552 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455616 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 9826346 d415 d416
private def d410 : MobiusHarmonicTree := .branch 24204524 d411 d414
private def d402 : MobiusHarmonicTree := .branch 55046120 d403 d410
private def d386 : MobiusHarmonicTree := .branch 101037789 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455680 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455744 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 11745623 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455808 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455872 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 13606971 d424 d425
private def d419 : MobiusHarmonicTree := .branch 25352594 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 455936 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456000 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 11000166 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456064 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456128 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 9948940 d431 d432
private def d426 : MobiusHarmonicTree := .branch 20949106 d427 d430
private def d418 : MobiusHarmonicTree := .branch 46301700 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456192 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456256 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 13676534 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456320 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456384 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 15675437 d439 d440
private def d434 : MobiusHarmonicTree := .branch 29351971 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456448 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456512 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 15947066 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456576 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456640 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 16338981 d446 d447
private def d441 : MobiusHarmonicTree := .branch 32286047 d442 d445
private def d433 : MobiusHarmonicTree := .branch 61638018 d434 d441
private def d417 : MobiusHarmonicTree := .branch 107939718 d418 d433
private def d385 : MobiusHarmonicTree := .branch 208977507 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456704 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456768 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 16174662 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456832 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456896 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 18214234 d456 d457
private def d451 : MobiusHarmonicTree := .branch 34388896 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 456960 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457024 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 19537364 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457088 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457152 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 21640416 d463 d464
private def d458 : MobiusHarmonicTree := .branch 41177780 d459 d462
private def d450 : MobiusHarmonicTree := .branch 75566676 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457216 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457280 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 24527748 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457344 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457408 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 23108594 d471 d472
private def d466 : MobiusHarmonicTree := .branch 47636342 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457472 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457536 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 23095619 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457600 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457664 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 22276259 d478 d479
private def d473 : MobiusHarmonicTree := .branch 45371878 d474 d477
private def d465 : MobiusHarmonicTree := .branch 93008220 d466 d473
private def d449 : MobiusHarmonicTree := .branch 168574896 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457728 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457792 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 22610709 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457856 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457920 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 27686009 d487 d488
private def d482 : MobiusHarmonicTree := .branch 50296718 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 457984 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458048 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 31688897 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458112 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458176 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 33834218 d494 d495
private def d489 : MobiusHarmonicTree := .branch 65523115 d490 d493
private def d481 : MobiusHarmonicTree := .branch 115819833 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458240 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458304 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 35171028 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458368 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458432 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 37283650 d502 d503
private def d497 : MobiusHarmonicTree := .branch 72454678 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458496 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458560 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 37993004 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458624 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock055 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 458688 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 35204848 d509 d510
private def d504 : MobiusHarmonicTree := .branch 73197852 d505 d508
private def d496 : MobiusHarmonicTree := .branch 145652530 d497 d504
private def d480 : MobiusHarmonicTree := .branch 261472363 d481 d496
private def d448 : MobiusHarmonicTree := .branch 430047259 d449 d480
private def d384 : MobiusHarmonicTree := .branch 639024766 d385 d448
private def d256 : MobiusHarmonicTree := .branch 910180752 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1608719646 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 442368 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 442368 1608719646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 442368 698538894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 442368 332816651 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 442368 160673743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 442368 58887586 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 442368 25495832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 442368 13109833 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 442368 6374005 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 442496 6735828 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 442624 12385999 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 442624 5285960 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 442752 7100039 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 442880 33391754 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 442880 13214318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 442880 6438864 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 443008 6775454 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 443136 20177436 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 443136 9020722 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 443264 11156714 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 443392 101786157 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 443392 48481418 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 443392 19672048 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 443392 9108180 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 443520 10563868 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 443648 28809370 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 443648 13628216 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 443776 15181154 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 443904 53304739 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 443904 27825063 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 443904 14814278 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 444032 13010785 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 444160 25479676 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 444160 13903083 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 444288 11576593 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 444416 172142908 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 444416 103631340 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 444416 44730769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 444416 24854590 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 444416 11717031 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 444544 13137559 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 444672 19876179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 444672 8933581 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 444800 10942598 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 444928 58900571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 444928 30557714 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 444928 14281171 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 445056 16276543 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 445184 28342857 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 445184 15959817 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 445312 12383040 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 445440 68511568 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 445440 41421167 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 445440 21453740 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 445440 11070622 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 445568 10383118 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 445696 19967427 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 445696 9478183 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 445824 10489244 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 445952 27090401 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 445952 15612345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 445952 9475214 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 446080 6137131 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 446208 11478056 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 446208 5893272 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 446336 5584784 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 446464 365722243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 446464 110803091 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 446464 29363162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 446464 12806677 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 446464 5839972 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 446464 3166835 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 446592 2673137 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 446720 6966705 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 446720 3216405 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 446848 3750300 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 446976 16556485 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 446976 6595785 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 446976 2867815 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 447104 3727970 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 447232 9960700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 447232 4616653 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 447360 5344047 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 447488 81439929 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 447488 34866314 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 447488 14614852 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 447488 6032850 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 447616 8582002 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 447744 20251462 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 447744 10227606 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 447872 10023856 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 448000 46573615 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 448000 19885235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 448000 10107971 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 448128 9777264 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 448256 26688380 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 448256 11038969 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 448384 15649411 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 448512 254919152 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 448512 151337071 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 448512 80784492 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 448512 41434181 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 448512 20424645 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 448640 21009536 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 448768 39350311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 448768 20348436 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 448896 19001875 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 449024 70552579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 449024 37571037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 449024 19049770 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 449152 18521267 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 449280 32981542 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 449280 17347649 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 449408 15633893 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 449536 103582081 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 449536 55394560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 449536 26929683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 449536 14904521 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 449664 12025162 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 449792 28464877 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 449792 13228657 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 449920 15236220 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 450048 48187521 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 450048 23358213 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 450048 13163534 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 450176 10194679 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 450304 24829308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 450304 11259713 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 450432 13569595 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 450560 910180752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 450560 271155986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 450560 132627174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 450560 93844831 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 450560 45504852 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 450560 24171824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 450560 11260044 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 450688 12911780 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 450816 21333028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 450816 10047150 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 450944 11285878 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 451072 48339979 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 451072 25507155 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 451072 11087606 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 451200 14419549 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 451328 22832824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 451328 10862042 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 451456 11970782 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 451584 38782343 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 451584 26129573 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 451584 16436015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 451584 9786560 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 451712 6649455 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 451840 9693558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 451840 5634033 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 451968 4059525 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 452096 12652770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 452096 3790467 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 452096 2419595 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 452224 1370872 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 452352 8862303 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 452352 3983111 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 452480 4879192 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 452608 138528812 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 452608 56088706 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 452608 31389545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 452608 13515275 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 452608 5323973 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 452736 8191302 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 452864 17874270 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 452864 7617169 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 452992 10257101 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 453120 24699161 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 453120 12737480 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 453120 7213562 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 453248 5523918 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 453376 11961681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 453376 3376427 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 453504 8585254 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 453632 82440106 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 453632 38573000 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 453632 21401227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 453632 10447592 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 453760 10953635 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 453888 17171773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 453888 9677326 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 454016 7494447 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 454144 43867106 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 454144 19741060 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 454144 8322157 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 454272 11418903 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 454400 24126046 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 454400 11393634 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 454528 12732412 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 454656 639024766 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 454656 208977507 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 454656 101037789 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 454656 45991669 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 454656 23648782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 454656 11840342 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 454784 11808440 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 454912 22342887 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 454912 9978662 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 455040 12364225 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 455168 55046120 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 455168 30841596 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 455168 15343879 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 455296 15497717 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 455424 24204524 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 455424 14378178 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 455552 9826346 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 455680 107939718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 455680 46301700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 455680 25352594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 455680 11745623 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 455808 13606971 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 455936 20949106 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 455936 11000166 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 456064 9948940 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 456192 61638018 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 456192 29351971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 456192 13676534 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 456320 15675437 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 456448 32286047 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 456448 15947066 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 456576 16338981 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 456704 430047259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 456704 168574896 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 456704 75566676 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 456704 34388896 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 456704 16174662 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 456832 18214234 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 456960 41177780 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 456960 19537364 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 457088 21640416 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 457216 93008220 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 457216 47636342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 457216 24527748 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 457344 23108594 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 457472 45371878 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 457472 23095619 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 457600 22276259 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 457728 261472363 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 457728 115819833 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 457728 50296718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 457728 22610709 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 457856 27686009 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 457984 65523115 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 457984 31688897 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 458112 33834218 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 458240 145652530 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 458240 72454678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 458240 35171028 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 458368 37283650 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 458496 73197852 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 458496 37993004 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 458624 35204848 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 442368 (MobiusHarmonicTree.branch 1608719646 mobiusHarmonicBlock054 mobiusHarmonicBlock055) = true := Helfgott.combined

#print axioms solution
