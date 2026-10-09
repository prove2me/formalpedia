-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair061_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:41:23.391576+00:00
-- url     : https://prove2.me/submissions/5697ecdc-87fe-4fa5-bb1b-5759f3eb854e

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999424 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999488 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 29154986 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999552 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999616 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 29415378 d11 d12
private def d6 : MobiusHarmonicTree := .branch 58570364 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999680 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999744 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 27874249 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999808 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999872 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 28065651 d18 d19
private def d13 : MobiusHarmonicTree := .branch 55939900 d14 d17
private def d5 : MobiusHarmonicTree := .branch 114510264 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999936 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000000 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 27655081 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000064 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000128 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 28387440 d26 d27
private def d21 : MobiusHarmonicTree := .branch 56042521 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000192 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000256 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 28099886 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000320 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000384 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 28526134 d33 d34
private def d28 : MobiusHarmonicTree := .branch 56626020 d29 d32
private def d20 : MobiusHarmonicTree := .branch 112668541 d21 d28
private def d4 : MobiusHarmonicTree := .branch 227178805 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000448 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000512 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 27492007 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000576 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000640 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 26156352 d42 d43
private def d37 : MobiusHarmonicTree := .branch 53648359 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000704 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000768 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 25303630 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000832 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000896 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 26039730 d49 d50
private def d44 : MobiusHarmonicTree := .branch 51343360 d45 d48
private def d36 : MobiusHarmonicTree := .branch 104991719 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1000960 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001024 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 26934497 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001088 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001152 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 26349699 d57 d58
private def d52 : MobiusHarmonicTree := .branch 53284196 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001216 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001280 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 26715890 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001344 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001408 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 27552274 d64 d65
private def d59 : MobiusHarmonicTree := .branch 54268164 d60 d63
private def d51 : MobiusHarmonicTree := .branch 107552360 d52 d59
private def d35 : MobiusHarmonicTree := .branch 212544079 d36 d51
private def d3 : MobiusHarmonicTree := .branch 439722884 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001472 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001536 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 28051008 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001600 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001664 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 28607483 d74 d75
private def d69 : MobiusHarmonicTree := .branch 56658491 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001728 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001792 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 28561881 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001856 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001920 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 29214974 d81 d82
private def d76 : MobiusHarmonicTree := .branch 57776855 d77 d80
private def d68 : MobiusHarmonicTree := .branch 114435346 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1001984 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002048 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 29893863 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002112 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002176 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 28704631 d89 d90
private def d84 : MobiusHarmonicTree := .branch 58598494 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002240 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002304 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 28817665 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002368 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002432 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 29308800 d96 d97
private def d91 : MobiusHarmonicTree := .branch 58126465 d92 d95
private def d83 : MobiusHarmonicTree := .branch 116724959 d84 d91
private def d67 : MobiusHarmonicTree := .branch 231160305 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002496 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002560 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 28132061 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002624 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002688 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 28049696 d105 d106
private def d100 : MobiusHarmonicTree := .branch 56181757 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002752 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002816 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 26818562 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002880 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1002944 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 25252750 d112 d113
private def d107 : MobiusHarmonicTree := .branch 52071312 d108 d111
private def d99 : MobiusHarmonicTree := .branch 108253069 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003008 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003072 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 25590465 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003136 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003200 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 25979923 d120 d121
private def d115 : MobiusHarmonicTree := .branch 51570388 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003264 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003328 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 25840099 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003392 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003456 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 24978748 d127 d128
private def d122 : MobiusHarmonicTree := .branch 50818847 d123 d126
private def d114 : MobiusHarmonicTree := .branch 102389235 d115 d122
private def d98 : MobiusHarmonicTree := .branch 210642304 d99 d114
private def d66 : MobiusHarmonicTree := .branch 441802609 d67 d98
private def d2 : MobiusHarmonicTree := .branch 881525493 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003520 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003584 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 25897272 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003648 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003712 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 25854120 d138 d139
private def d133 : MobiusHarmonicTree := .branch 51751392 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003776 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003840 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 24310723 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003904 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1003968 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 23101428 d145 d146
private def d140 : MobiusHarmonicTree := .branch 47412151 d141 d144
private def d132 : MobiusHarmonicTree := .branch 99163543 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004032 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004096 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 21468156 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004160 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004224 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 21821888 d153 d154
private def d148 : MobiusHarmonicTree := .branch 43290044 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004288 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004352 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 23566483 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004416 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004480 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 24667554 d160 d161
private def d155 : MobiusHarmonicTree := .branch 48234037 d156 d159
private def d147 : MobiusHarmonicTree := .branch 91524081 d148 d155
private def d131 : MobiusHarmonicTree := .branch 190687624 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004544 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004608 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 24410609 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004672 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004736 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 22314419 d169 d170
private def d164 : MobiusHarmonicTree := .branch 46725028 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004800 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004864 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 22858866 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004928 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1004992 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 22852004 d176 d177
private def d171 : MobiusHarmonicTree := .branch 45710870 d172 d175
private def d163 : MobiusHarmonicTree := .branch 92435898 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005056 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005120 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 22530718 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005184 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005248 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 21761881 d184 d185
private def d179 : MobiusHarmonicTree := .branch 44292599 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005312 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005376 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 21353279 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005440 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005504 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 21093972 d191 d192
private def d186 : MobiusHarmonicTree := .branch 42447251 d187 d190
private def d178 : MobiusHarmonicTree := .branch 86739850 d179 d186
private def d162 : MobiusHarmonicTree := .branch 179175748 d163 d178
private def d130 : MobiusHarmonicTree := .branch 369863372 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005568 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005632 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 21494013 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005696 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005760 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 21863139 d201 d202
private def d196 : MobiusHarmonicTree := .branch 43357152 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005824 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005888 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 22317669 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1005952 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006016 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 21487812 d208 d209
private def d203 : MobiusHarmonicTree := .branch 43805481 d204 d207
private def d195 : MobiusHarmonicTree := .branch 87162633 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006080 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006144 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 20755568 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006208 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006272 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 19015816 d216 d217
private def d211 : MobiusHarmonicTree := .branch 39771384 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006336 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006400 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 18476809 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006464 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006528 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 18538078 d223 d224
private def d218 : MobiusHarmonicTree := .branch 37014887 d219 d222
private def d210 : MobiusHarmonicTree := .branch 76786271 d211 d218
private def d194 : MobiusHarmonicTree := .branch 163948904 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006592 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006656 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 18078728 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006720 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006784 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 18889921 d232 d233
private def d227 : MobiusHarmonicTree := .branch 36968649 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006848 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006912 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 18376066 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1006976 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007040 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 17648827 d239 d240
private def d234 : MobiusHarmonicTree := .branch 36024893 d235 d238
private def d226 : MobiusHarmonicTree := .branch 72993542 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007104 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007168 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 17752826 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007232 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007296 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 18311482 d247 d248
private def d242 : MobiusHarmonicTree := .branch 36064308 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007360 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007424 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 17731424 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007488 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock122 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007552 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 18046758 d254 d255
private def d249 : MobiusHarmonicTree := .branch 35778182 d250 d253
private def d241 : MobiusHarmonicTree := .branch 71842490 d242 d249
private def d225 : MobiusHarmonicTree := .branch 144836032 d226 d241
private def d193 : MobiusHarmonicTree := .branch 308784936 d194 d225
private def d129 : MobiusHarmonicTree := .branch 678648308 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1560173801 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007616 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007680 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 18797704 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007744 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007808 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 18433160 d266 d267
private def d261 : MobiusHarmonicTree := .branch 37230864 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007872 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1007936 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 18032985 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008000 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008064 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 18166574 d273 d274
private def d268 : MobiusHarmonicTree := .branch 36199559 d269 d272
private def d260 : MobiusHarmonicTree := .branch 73430423 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008128 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008192 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 17814148 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008256 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008320 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 17507398 d281 d282
private def d276 : MobiusHarmonicTree := .branch 35321546 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008384 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008448 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 17103600 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008512 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008576 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 15221550 d288 d289
private def d283 : MobiusHarmonicTree := .branch 32325150 d284 d287
private def d275 : MobiusHarmonicTree := .branch 67646696 d276 d283
private def d259 : MobiusHarmonicTree := .branch 141077119 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008640 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008704 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 16080090 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008768 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008832 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 16433942 d297 d298
private def d292 : MobiusHarmonicTree := .branch 32514032 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008896 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1008960 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 16470474 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009024 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009088 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 17022377 d304 d305
private def d299 : MobiusHarmonicTree := .branch 33492851 d300 d303
private def d291 : MobiusHarmonicTree := .branch 66006883 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009152 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009216 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 17299637 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009280 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009344 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 15857913 d312 d313
private def d307 : MobiusHarmonicTree := .branch 33157550 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009408 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009472 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 16292745 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009536 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009600 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 16026227 d319 d320
private def d314 : MobiusHarmonicTree := .branch 32318972 d315 d318
private def d306 : MobiusHarmonicTree := .branch 65476522 d307 d314
private def d290 : MobiusHarmonicTree := .branch 131483405 d291 d306
private def d258 : MobiusHarmonicTree := .branch 272560524 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009664 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009728 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 15893429 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009792 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009856 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 17097546 d329 d330
private def d324 : MobiusHarmonicTree := .branch 32990975 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009920 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1009984 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 18160754 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010048 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010112 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 19299909 d336 d337
private def d331 : MobiusHarmonicTree := .branch 37460663 d332 d335
private def d323 : MobiusHarmonicTree := .branch 70451638 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010176 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010240 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 20642671 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010304 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010368 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 22949125 d344 d345
private def d339 : MobiusHarmonicTree := .branch 43591796 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010432 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010496 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 23514283 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010560 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010624 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 24123768 d351 d352
private def d346 : MobiusHarmonicTree := .branch 47638051 d347 d350
private def d338 : MobiusHarmonicTree := .branch 91229847 d339 d346
private def d322 : MobiusHarmonicTree := .branch 161681485 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010688 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010752 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 24409652 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010816 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010880 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 22424102 d360 d361
private def d355 : MobiusHarmonicTree := .branch 46833754 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1010944 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011008 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 22554798 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011072 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011136 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 22821925 d367 d368
private def d362 : MobiusHarmonicTree := .branch 45376723 d363 d366
private def d354 : MobiusHarmonicTree := .branch 92210477 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011200 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011264 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 23048465 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011328 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011392 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 23434096 d375 d376
private def d370 : MobiusHarmonicTree := .branch 46482561 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011456 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011520 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 24989205 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011584 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011648 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 25147151 d382 d383
private def d377 : MobiusHarmonicTree := .branch 50136356 d378 d381
private def d369 : MobiusHarmonicTree := .branch 96618917 d370 d377
private def d353 : MobiusHarmonicTree := .branch 188829394 d354 d369
private def d321 : MobiusHarmonicTree := .branch 350510879 d322 d353
private def d257 : MobiusHarmonicTree := .branch 623071403 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011712 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011776 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 24715059 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011840 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011904 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 24037921 d393 d394
private def d388 : MobiusHarmonicTree := .branch 48752980 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1011968 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012032 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 23891633 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012096 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012160 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 22055878 d400 d401
private def d395 : MobiusHarmonicTree := .branch 45947511 d396 d399
private def d387 : MobiusHarmonicTree := .branch 94700491 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012224 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012288 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 20994125 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012352 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012416 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 20847254 d408 d409
private def d403 : MobiusHarmonicTree := .branch 41841379 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012480 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012544 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 20563126 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012608 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012672 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 20882470 d415 d416
private def d410 : MobiusHarmonicTree := .branch 41445596 d411 d414
private def d402 : MobiusHarmonicTree := .branch 83286975 d403 d410
private def d386 : MobiusHarmonicTree := .branch 177987466 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012736 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012800 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 19716706 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012864 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012928 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 20686628 d424 d425
private def d419 : MobiusHarmonicTree := .branch 40403334 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1012992 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013056 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 21167684 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013120 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013184 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 22290206 d431 d432
private def d426 : MobiusHarmonicTree := .branch 43457890 d427 d430
private def d418 : MobiusHarmonicTree := .branch 83861224 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013248 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013312 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 21893631 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013376 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013440 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 21209024 d439 d440
private def d434 : MobiusHarmonicTree := .branch 43102655 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013504 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013568 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 21768706 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013632 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013696 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 21906039 d446 d447
private def d441 : MobiusHarmonicTree := .branch 43674745 d442 d445
private def d433 : MobiusHarmonicTree := .branch 86777400 d434 d441
private def d417 : MobiusHarmonicTree := .branch 170638624 d418 d433
private def d385 : MobiusHarmonicTree := .branch 348626090 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013760 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013824 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 21854965 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013888 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1013952 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 21618440 d456 d457
private def d451 : MobiusHarmonicTree := .branch 43473405 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014016 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014080 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 22641281 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014144 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014208 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 22192769 d463 d464
private def d458 : MobiusHarmonicTree := .branch 44834050 d459 d462
private def d450 : MobiusHarmonicTree := .branch 88307455 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014272 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014336 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 22064751 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014400 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014464 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 22615964 d471 d472
private def d466 : MobiusHarmonicTree := .branch 44680715 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014528 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014592 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 22217883 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014656 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014720 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 23178858 d478 d479
private def d473 : MobiusHarmonicTree := .branch 45396741 d474 d477
private def d465 : MobiusHarmonicTree := .branch 90077456 d466 d473
private def d449 : MobiusHarmonicTree := .branch 178384911 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014784 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014848 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 24240143 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014912 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1014976 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 24770120 d487 d488
private def d482 : MobiusHarmonicTree := .branch 49010263 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015040 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015104 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 23078523 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015168 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015232 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 23761130 d494 d495
private def d489 : MobiusHarmonicTree := .branch 46839653 d490 d493
private def d481 : MobiusHarmonicTree := .branch 95849916 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015296 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015360 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 24215147 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015424 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015488 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 22807853 d502 d503
private def d497 : MobiusHarmonicTree := .branch 47023000 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015552 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015616 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 21614548 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015680 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock123 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1015744 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 21346017 d509 d510
private def d504 : MobiusHarmonicTree := .branch 42960565 d505 d508
private def d496 : MobiusHarmonicTree := .branch 89983565 d497 d504
private def d480 : MobiusHarmonicTree := .branch 185833481 d481 d496
private def d448 : MobiusHarmonicTree := .branch 364218392 d449 d480
private def d384 : MobiusHarmonicTree := .branch 712844482 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1335915885 d257 d384
private def d0 : MobiusHarmonicTree := .branch 2896089686 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 999424 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 999424 2896089686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 999424 1560173801 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 999424 881525493 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 999424 439722884 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 999424 227178805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 999424 114510264 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 999424 58570364 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 999424 29154986 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 999552 29415378 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 999680 55939900 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 999680 27874249 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 999808 28065651 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 999936 112668541 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 999936 56042521 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 999936 27655081 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1000064 28387440 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1000192 56626020 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1000192 28099886 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1000320 28526134 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1000448 212544079 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1000448 104991719 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1000448 53648359 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1000448 27492007 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1000576 26156352 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1000704 51343360 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1000704 25303630 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1000832 26039730 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1000960 107552360 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1000960 53284196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1000960 26934497 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1001088 26349699 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1001216 54268164 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1001216 26715890 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1001344 27552274 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1001472 441802609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1001472 231160305 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1001472 114435346 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1001472 56658491 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1001472 28051008 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1001600 28607483 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1001728 57776855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1001728 28561881 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1001856 29214974 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1001984 116724959 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1001984 58598494 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1001984 29893863 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1002112 28704631 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1002240 58126465 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1002240 28817665 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1002368 29308800 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1002496 210642304 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1002496 108253069 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1002496 56181757 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1002496 28132061 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1002624 28049696 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1002752 52071312 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1002752 26818562 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1002880 25252750 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1003008 102389235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1003008 51570388 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1003008 25590465 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1003136 25979923 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1003264 50818847 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1003264 25840099 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1003392 24978748 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1003520 678648308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1003520 369863372 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1003520 190687624 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1003520 99163543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1003520 51751392 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1003520 25897272 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1003648 25854120 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1003776 47412151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1003776 24310723 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1003904 23101428 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1004032 91524081 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1004032 43290044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1004032 21468156 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1004160 21821888 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1004288 48234037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1004288 23566483 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1004416 24667554 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1004544 179175748 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1004544 92435898 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1004544 46725028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1004544 24410609 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1004672 22314419 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1004800 45710870 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1004800 22858866 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1004928 22852004 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1005056 86739850 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1005056 44292599 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1005056 22530718 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1005184 21761881 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1005312 42447251 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1005312 21353279 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1005440 21093972 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1005568 308784936 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1005568 163948904 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1005568 87162633 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1005568 43357152 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1005568 21494013 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1005696 21863139 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1005824 43805481 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1005824 22317669 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1005952 21487812 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1006080 76786271 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1006080 39771384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1006080 20755568 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1006208 19015816 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1006336 37014887 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1006336 18476809 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1006464 18538078 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1006592 144836032 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1006592 72993542 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1006592 36968649 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1006592 18078728 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1006720 18889921 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1006848 36024893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1006848 18376066 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1006976 17648827 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1007104 71842490 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1007104 36064308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1007104 17752826 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1007232 18311482 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1007360 35778182 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1007360 17731424 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1007488 18046758 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 1007616 1335915885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1007616 623071403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1007616 272560524 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1007616 141077119 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1007616 73430423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1007616 37230864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1007616 18797704 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1007744 18433160 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1007872 36199559 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1007872 18032985 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1008000 18166574 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1008128 67646696 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1008128 35321546 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1008128 17814148 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1008256 17507398 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1008384 32325150 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1008384 17103600 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1008512 15221550 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1008640 131483405 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1008640 66006883 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1008640 32514032 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1008640 16080090 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1008768 16433942 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1008896 33492851 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1008896 16470474 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1009024 17022377 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1009152 65476522 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1009152 33157550 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1009152 17299637 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1009280 15857913 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1009408 32318972 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1009408 16292745 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1009536 16026227 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1009664 350510879 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1009664 161681485 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1009664 70451638 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1009664 32990975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1009664 15893429 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1009792 17097546 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1009920 37460663 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1009920 18160754 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1010048 19299909 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1010176 91229847 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1010176 43591796 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1010176 20642671 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1010304 22949125 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1010432 47638051 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1010432 23514283 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1010560 24123768 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1010688 188829394 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1010688 92210477 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1010688 46833754 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1010688 24409652 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1010816 22424102 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1010944 45376723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1010944 22554798 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1011072 22821925 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1011200 96618917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1011200 46482561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1011200 23048465 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1011328 23434096 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1011456 50136356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1011456 24989205 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1011584 25147151 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1011712 712844482 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1011712 348626090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1011712 177987466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1011712 94700491 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1011712 48752980 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1011712 24715059 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1011840 24037921 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1011968 45947511 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1011968 23891633 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1012096 22055878 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1012224 83286975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1012224 41841379 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1012224 20994125 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1012352 20847254 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1012480 41445596 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1012480 20563126 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1012608 20882470 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1012736 170638624 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1012736 83861224 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1012736 40403334 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1012736 19716706 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1012864 20686628 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1012992 43457890 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1012992 21167684 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1013120 22290206 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1013248 86777400 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1013248 43102655 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1013248 21893631 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1013376 21209024 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1013504 43674745 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1013504 21768706 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1013632 21906039 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1013760 364218392 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1013760 178384911 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1013760 88307455 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1013760 43473405 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1013760 21854965 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1013888 21618440 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1014016 44834050 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1014016 22641281 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1014144 22192769 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1014272 90077456 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1014272 44680715 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1014272 22064751 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1014400 22615964 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1014528 45396741 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1014528 22217883 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1014656 23178858 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1014784 185833481 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1014784 95849916 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1014784 49010263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1014784 24240143 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1014912 24770120 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1015040 46839653 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1015040 23078523 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1015168 23761130 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1015296 89983565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1015296 47023000 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1015296 24215147 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1015424 22807853 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1015552 42960565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1015552 21614548 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1015680 21346017 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 999424 (MobiusHarmonicTree.branch 2896089686 mobiusHarmonicBlock122 mobiusHarmonicBlock123) = true := Helfgott.combined

#print axioms solution
