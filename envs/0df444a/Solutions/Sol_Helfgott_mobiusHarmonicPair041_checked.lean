-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair041_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:27:06.052418+00:00
-- url     : https://prove2.me/submissions/d5cf3ec5-a327-418a-8576-19dff74d62ed

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 671744 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 671808 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 47204081 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 671872 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 671936 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 44468676 d11 d12
private def d6 : MobiusHarmonicTree := .branch 91672757 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672000 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672064 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 41857755 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672128 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672192 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 39845862 d18 d19
private def d13 : MobiusHarmonicTree := .branch 81703617 d14 d17
private def d5 : MobiusHarmonicTree := .branch 173376374 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672256 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672320 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 38693027 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672384 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672448 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 38782235 d26 d27
private def d21 : MobiusHarmonicTree := .branch 77475262 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672512 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672576 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 40731491 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672640 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672704 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 42158291 d33 d34
private def d28 : MobiusHarmonicTree := .branch 82889782 d29 d32
private def d20 : MobiusHarmonicTree := .branch 160365044 d21 d28
private def d4 : MobiusHarmonicTree := .branch 333741418 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672768 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672832 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 40351963 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672896 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 672960 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 38272791 d42 d43
private def d37 : MobiusHarmonicTree := .branch 78624754 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673024 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673088 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 38663711 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673152 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673216 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 38527093 d49 d50
private def d44 : MobiusHarmonicTree := .branch 77190804 d45 d48
private def d36 : MobiusHarmonicTree := .branch 155815558 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673280 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673344 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 38745503 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673408 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673472 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 38674316 d57 d58
private def d52 : MobiusHarmonicTree := .branch 77419819 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673536 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673600 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 39623007 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673664 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673728 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 38831813 d64 d65
private def d59 : MobiusHarmonicTree := .branch 78454820 d60 d63
private def d51 : MobiusHarmonicTree := .branch 155874639 d52 d59
private def d35 : MobiusHarmonicTree := .branch 311690197 d36 d51
private def d3 : MobiusHarmonicTree := .branch 645431615 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673792 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673856 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 38208505 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673920 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 673984 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 38670171 d74 d75
private def d69 : MobiusHarmonicTree := .branch 76878676 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674048 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674112 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 37363315 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674176 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674240 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 38901644 d81 d82
private def d76 : MobiusHarmonicTree := .branch 76264959 d77 d80
private def d68 : MobiusHarmonicTree := .branch 153143635 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674304 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674368 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 39196785 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674432 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674496 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 39697929 d89 d90
private def d84 : MobiusHarmonicTree := .branch 78894714 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674560 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674624 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 39542082 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674688 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674752 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 39444247 d96 d97
private def d91 : MobiusHarmonicTree := .branch 78986329 d92 d95
private def d83 : MobiusHarmonicTree := .branch 157881043 d84 d91
private def d67 : MobiusHarmonicTree := .branch 311024678 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674816 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674880 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 37286750 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 674944 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675008 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 36278178 d105 d106
private def d100 : MobiusHarmonicTree := .branch 73564928 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675072 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675136 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 36386875 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675200 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675264 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 36080797 d112 d113
private def d107 : MobiusHarmonicTree := .branch 72467672 d108 d111
private def d99 : MobiusHarmonicTree := .branch 146032600 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675328 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675392 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 37255493 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675456 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675520 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 37279513 d120 d121
private def d115 : MobiusHarmonicTree := .branch 74535006 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675584 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675648 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 36590146 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675712 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675776 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 37531769 d127 d128
private def d122 : MobiusHarmonicTree := .branch 74121915 d123 d126
private def d114 : MobiusHarmonicTree := .branch 148656921 d115 d122
private def d98 : MobiusHarmonicTree := .branch 294689521 d99 d114
private def d66 : MobiusHarmonicTree := .branch 605714199 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1251145814 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675840 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675904 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 37731771 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 675968 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676032 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 36885916 d138 d139
private def d133 : MobiusHarmonicTree := .branch 74617687 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676096 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676160 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 35865886 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676224 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676288 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 37139552 d145 d146
private def d140 : MobiusHarmonicTree := .branch 73005438 d141 d144
private def d132 : MobiusHarmonicTree := .branch 147623125 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676352 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676416 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 38693732 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676480 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676544 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 39428412 d153 d154
private def d148 : MobiusHarmonicTree := .branch 78122144 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676608 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676672 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 41673135 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676736 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676800 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 42232646 d160 d161
private def d155 : MobiusHarmonicTree := .branch 83905781 d156 d159
private def d147 : MobiusHarmonicTree := .branch 162027925 d148 d155
private def d131 : MobiusHarmonicTree := .branch 309651050 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676864 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676928 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 44801017 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 676992 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677056 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 43910788 d169 d170
private def d164 : MobiusHarmonicTree := .branch 88711805 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677120 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677184 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 45816289 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677248 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677312 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 45603874 d176 d177
private def d171 : MobiusHarmonicTree := .branch 91420163 d172 d175
private def d163 : MobiusHarmonicTree := .branch 180131968 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677376 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677440 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 47325320 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677504 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677568 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 46848565 d184 d185
private def d179 : MobiusHarmonicTree := .branch 94173885 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677632 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677696 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 46724581 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677760 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677824 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 46044501 d191 d192
private def d186 : MobiusHarmonicTree := .branch 92769082 d187 d190
private def d178 : MobiusHarmonicTree := .branch 186942967 d179 d186
private def d162 : MobiusHarmonicTree := .branch 367074935 d163 d178
private def d130 : MobiusHarmonicTree := .branch 676725985 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677888 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 677952 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 47472477 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678016 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678080 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 47426697 d201 d202
private def d196 : MobiusHarmonicTree := .branch 94899174 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678144 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678208 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 45996326 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678272 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678336 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 46572852 d208 d209
private def d203 : MobiusHarmonicTree := .branch 92569178 d204 d207
private def d195 : MobiusHarmonicTree := .branch 187468352 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678400 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678464 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 45827178 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678528 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678592 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 44763406 d216 d217
private def d211 : MobiusHarmonicTree := .branch 90590584 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678656 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678720 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 43165218 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678784 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678848 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 39154720 d223 d224
private def d218 : MobiusHarmonicTree := .branch 82319938 d219 d222
private def d210 : MobiusHarmonicTree := .branch 172910522 d211 d218
private def d194 : MobiusHarmonicTree := .branch 360378874 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678912 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 678976 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 37014684 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679040 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679104 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 35857627 d232 d233
private def d227 : MobiusHarmonicTree := .branch 72872311 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679168 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679232 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 37399665 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679296 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679360 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 36170956 d239 d240
private def d234 : MobiusHarmonicTree := .branch 73570621 d235 d238
private def d226 : MobiusHarmonicTree := .branch 146442932 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679424 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679488 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 33822602 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679552 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679616 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 33928087 d247 d248
private def d242 : MobiusHarmonicTree := .branch 67750689 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679680 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679744 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 33122881 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679808 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock082 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679872 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 31322189 d254 d255
private def d249 : MobiusHarmonicTree := .branch 64445070 d250 d253
private def d241 : MobiusHarmonicTree := .branch 132195759 d242 d249
private def d225 : MobiusHarmonicTree := .branch 278638691 d226 d241
private def d193 : MobiusHarmonicTree := .branch 639017565 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1315743550 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2566889364 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 679936 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680000 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 29036909 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680064 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680128 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 29129864 d266 d267
private def d261 : MobiusHarmonicTree := .branch 58166773 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680192 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680256 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 30591485 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680320 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680384 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 29318839 d273 d274
private def d268 : MobiusHarmonicTree := .branch 59910324 d269 d272
private def d260 : MobiusHarmonicTree := .branch 118077097 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680448 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680512 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 28627043 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680576 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680640 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 27885624 d281 d282
private def d276 : MobiusHarmonicTree := .branch 56512667 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680704 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680768 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 27670295 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680832 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680896 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 27910371 d288 d289
private def d283 : MobiusHarmonicTree := .branch 55580666 d284 d287
private def d275 : MobiusHarmonicTree := .branch 112093333 d276 d283
private def d259 : MobiusHarmonicTree := .branch 230170430 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 680960 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681024 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 27285542 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681088 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681152 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 23444206 d297 d298
private def d292 : MobiusHarmonicTree := .branch 50729748 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681216 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681280 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 23473503 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681344 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681408 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 24624068 d304 d305
private def d299 : MobiusHarmonicTree := .branch 48097571 d300 d303
private def d291 : MobiusHarmonicTree := .branch 98827319 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681472 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681536 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 25031781 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681600 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681664 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 26143449 d312 d313
private def d307 : MobiusHarmonicTree := .branch 51175230 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681728 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681792 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 27100661 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681856 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681920 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 30905450 d319 d320
private def d314 : MobiusHarmonicTree := .branch 58006111 d315 d318
private def d306 : MobiusHarmonicTree := .branch 109181341 d307 d314
private def d290 : MobiusHarmonicTree := .branch 208008660 d291 d306
private def d258 : MobiusHarmonicTree := .branch 438179090 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 681984 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682048 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 31625410 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682112 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682176 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 32072445 d329 d330
private def d324 : MobiusHarmonicTree := .branch 63697855 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682240 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682304 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 30376635 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682368 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682432 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 28421985 d336 d337
private def d331 : MobiusHarmonicTree := .branch 58798620 d332 d335
private def d323 : MobiusHarmonicTree := .branch 122496475 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682496 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682560 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 28623172 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682624 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682688 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 30391713 d344 d345
private def d339 : MobiusHarmonicTree := .branch 59014885 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682752 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682816 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 29439930 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682880 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 682944 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 31829901 d351 d352
private def d346 : MobiusHarmonicTree := .branch 61269831 d347 d350
private def d338 : MobiusHarmonicTree := .branch 120284716 d339 d346
private def d322 : MobiusHarmonicTree := .branch 242781191 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683008 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683072 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 34363914 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683136 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683200 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 35781655 d360 d361
private def d355 : MobiusHarmonicTree := .branch 70145569 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683264 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683328 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 37310131 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683392 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683456 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 35605934 d367 d368
private def d362 : MobiusHarmonicTree := .branch 72916065 d363 d366
private def d354 : MobiusHarmonicTree := .branch 143061634 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683520 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683584 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 36687555 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683648 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683712 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 36753880 d375 d376
private def d370 : MobiusHarmonicTree := .branch 73441435 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683776 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683840 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 33921839 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683904 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 683968 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 31896324 d382 d383
private def d377 : MobiusHarmonicTree := .branch 65818163 d378 d381
private def d369 : MobiusHarmonicTree := .branch 139259598 d370 d377
private def d353 : MobiusHarmonicTree := .branch 282321232 d354 d369
private def d321 : MobiusHarmonicTree := .branch 525102423 d322 d353
private def d257 : MobiusHarmonicTree := .branch 963281513 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684032 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684096 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 32698689 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684160 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684224 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 33796039 d393 d394
private def d388 : MobiusHarmonicTree := .branch 66494728 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684288 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684352 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 34710289 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684416 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684480 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 34525601 d400 d401
private def d395 : MobiusHarmonicTree := .branch 69235890 d396 d399
private def d387 : MobiusHarmonicTree := .branch 135730618 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684544 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684608 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 33791690 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684672 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684736 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 35104092 d408 d409
private def d403 : MobiusHarmonicTree := .branch 68895782 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684800 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684864 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 35466999 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684928 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 684992 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 35626816 d415 d416
private def d410 : MobiusHarmonicTree := .branch 71093815 d411 d414
private def d402 : MobiusHarmonicTree := .branch 139989597 d403 d410
private def d386 : MobiusHarmonicTree := .branch 275720215 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685056 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685120 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 33400102 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685184 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685248 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 33223107 d424 d425
private def d419 : MobiusHarmonicTree := .branch 66623209 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685312 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685376 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 33368621 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685440 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685504 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 33120273 d431 d432
private def d426 : MobiusHarmonicTree := .branch 66488894 d427 d430
private def d418 : MobiusHarmonicTree := .branch 133112103 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685568 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685632 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 32809264 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685696 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685760 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 32756421 d439 d440
private def d434 : MobiusHarmonicTree := .branch 65565685 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685824 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685888 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 34699614 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 685952 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686016 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 32967304 d446 d447
private def d441 : MobiusHarmonicTree := .branch 67666918 d442 d445
private def d433 : MobiusHarmonicTree := .branch 133232603 d434 d441
private def d417 : MobiusHarmonicTree := .branch 266344706 d418 d433
private def d385 : MobiusHarmonicTree := .branch 542064921 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686080 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686144 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 31961323 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686208 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686272 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 31685777 d456 d457
private def d451 : MobiusHarmonicTree := .branch 63647100 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686336 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686400 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 31290846 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686464 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686528 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 33257254 d463 d464
private def d458 : MobiusHarmonicTree := .branch 64548100 d459 d462
private def d450 : MobiusHarmonicTree := .branch 128195200 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686592 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686656 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 34660801 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686720 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686784 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 34671838 d471 d472
private def d466 : MobiusHarmonicTree := .branch 69332639 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686848 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686912 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 34224255 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 686976 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687040 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 33753584 d478 d479
private def d473 : MobiusHarmonicTree := .branch 67977839 d474 d477
private def d465 : MobiusHarmonicTree := .branch 137310478 d466 d473
private def d449 : MobiusHarmonicTree := .branch 265505678 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687104 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687168 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 33648311 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687232 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687296 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 35974424 d487 d488
private def d482 : MobiusHarmonicTree := .branch 69622735 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687360 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687424 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 35887701 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687488 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687552 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 34948716 d494 d495
private def d489 : MobiusHarmonicTree := .branch 70836417 d490 d493
private def d481 : MobiusHarmonicTree := .branch 140459152 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687616 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687680 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 35180735 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687744 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687808 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 33403337 d502 d503
private def d497 : MobiusHarmonicTree := .branch 68584072 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687872 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 687936 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 31898414 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688000 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock083 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 688064 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 32183154 d509 d510
private def d504 : MobiusHarmonicTree := .branch 64081568 d505 d508
private def d496 : MobiusHarmonicTree := .branch 132665640 d497 d504
private def d480 : MobiusHarmonicTree := .branch 273124792 d481 d496
private def d448 : MobiusHarmonicTree := .branch 538630470 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1080695391 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2043976904 d257 d384
private def d0 : MobiusHarmonicTree := .branch 4610866268 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 671744 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 671744 4610866268 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 671744 2566889364 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 671744 1251145814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 671744 645431615 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 671744 333741418 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 671744 173376374 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 671744 91672757 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 671744 47204081 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 671872 44468676 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 672000 81703617 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 672000 41857755 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 672128 39845862 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 672256 160365044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 672256 77475262 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 672256 38693027 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 672384 38782235 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 672512 82889782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 672512 40731491 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 672640 42158291 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 672768 311690197 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 672768 155815558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 672768 78624754 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 672768 40351963 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 672896 38272791 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 673024 77190804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 673024 38663711 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 673152 38527093 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 673280 155874639 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 673280 77419819 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 673280 38745503 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 673408 38674316 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 673536 78454820 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 673536 39623007 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 673664 38831813 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 673792 605714199 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 673792 311024678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 673792 153143635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 673792 76878676 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 673792 38208505 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 673920 38670171 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 674048 76264959 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 674048 37363315 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 674176 38901644 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 674304 157881043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 674304 78894714 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 674304 39196785 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 674432 39697929 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 674560 78986329 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 674560 39542082 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 674688 39444247 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 674816 294689521 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 674816 146032600 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 674816 73564928 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 674816 37286750 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 674944 36278178 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 675072 72467672 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 675072 36386875 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 675200 36080797 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 675328 148656921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 675328 74535006 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 675328 37255493 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 675456 37279513 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 675584 74121915 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 675584 36590146 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 675712 37531769 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 675840 1315743550 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 675840 676725985 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 675840 309651050 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 675840 147623125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 675840 74617687 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 675840 37731771 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 675968 36885916 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 676096 73005438 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 676096 35865886 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 676224 37139552 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 676352 162027925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 676352 78122144 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 676352 38693732 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 676480 39428412 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 676608 83905781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 676608 41673135 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 676736 42232646 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 676864 367074935 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 676864 180131968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 676864 88711805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 676864 44801017 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 676992 43910788 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 677120 91420163 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 677120 45816289 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 677248 45603874 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 677376 186942967 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 677376 94173885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 677376 47325320 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 677504 46848565 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 677632 92769082 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 677632 46724581 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 677760 46044501 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 677888 639017565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 677888 360378874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 677888 187468352 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 677888 94899174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 677888 47472477 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 678016 47426697 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 678144 92569178 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 678144 45996326 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 678272 46572852 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 678400 172910522 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 678400 90590584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 678400 45827178 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 678528 44763406 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 678656 82319938 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 678656 43165218 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 678784 39154720 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 678912 278638691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 678912 146442932 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 678912 72872311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 678912 37014684 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 679040 35857627 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 679168 73570621 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 679168 37399665 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 679296 36170956 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 679424 132195759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 679424 67750689 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 679424 33822602 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 679552 33928087 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 679680 64445070 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 679680 33122881 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 679808 31322189 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 679936 2043976904 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 679936 963281513 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 679936 438179090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 679936 230170430 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 679936 118077097 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 679936 58166773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 679936 29036909 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 680064 29129864 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 680192 59910324 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 680192 30591485 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 680320 29318839 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 680448 112093333 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 680448 56512667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 680448 28627043 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 680576 27885624 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 680704 55580666 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 680704 27670295 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 680832 27910371 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 680960 208008660 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 680960 98827319 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 680960 50729748 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 680960 27285542 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 681088 23444206 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 681216 48097571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 681216 23473503 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 681344 24624068 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 681472 109181341 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 681472 51175230 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 681472 25031781 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 681600 26143449 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 681728 58006111 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 681728 27100661 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 681856 30905450 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 681984 525102423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 681984 242781191 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 681984 122496475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 681984 63697855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 681984 31625410 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 682112 32072445 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 682240 58798620 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 682240 30376635 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 682368 28421985 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 682496 120284716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 682496 59014885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 682496 28623172 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 682624 30391713 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 682752 61269831 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 682752 29439930 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 682880 31829901 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 683008 282321232 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 683008 143061634 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 683008 70145569 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 683008 34363914 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 683136 35781655 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 683264 72916065 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 683264 37310131 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 683392 35605934 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 683520 139259598 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 683520 73441435 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 683520 36687555 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 683648 36753880 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 683776 65818163 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 683776 33921839 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 683904 31896324 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 684032 1080695391 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 684032 542064921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 684032 275720215 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 684032 135730618 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 684032 66494728 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 684032 32698689 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 684160 33796039 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 684288 69235890 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 684288 34710289 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 684416 34525601 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 684544 139989597 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 684544 68895782 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 684544 33791690 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 684672 35104092 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 684800 71093815 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 684800 35466999 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 684928 35626816 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 685056 266344706 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 685056 133112103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 685056 66623209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 685056 33400102 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 685184 33223107 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 685312 66488894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 685312 33368621 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 685440 33120273 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 685568 133232603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 685568 65565685 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 685568 32809264 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 685696 32756421 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 685824 67666918 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 685824 34699614 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 685952 32967304 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 686080 538630470 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 686080 265505678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 686080 128195200 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 686080 63647100 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 686080 31961323 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 686208 31685777 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 686336 64548100 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 686336 31290846 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 686464 33257254 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 686592 137310478 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 686592 69332639 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 686592 34660801 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 686720 34671838 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 686848 67977839 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 686848 34224255 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 686976 33753584 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 687104 273124792 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 687104 140459152 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 687104 69622735 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 687104 33648311 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 687232 35974424 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 687360 70836417 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 687360 35887701 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 687488 34948716 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 687616 132665640 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 687616 68584072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 687616 35180735 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 687744 33403337 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 687872 64081568 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 687872 31898414 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 688000 32183154 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 671744 (MobiusHarmonicTree.branch 4610866268 mobiusHarmonicBlock082 mobiusHarmonicBlock083) = true := Helfgott.combined

#print axioms solution
