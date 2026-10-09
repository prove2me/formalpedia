-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair037_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:12:13.230749+00:00
-- url     : https://prove2.me/submissions/fbfbeb43-06d4-46de-9389-46834c032533

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606208 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606272 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 40816776 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606336 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606400 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 40128727 d11 d12
private def d6 : MobiusHarmonicTree := .branch 80945503 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606464 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606528 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 43239639 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606592 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606656 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 42829961 d18 d19
private def d13 : MobiusHarmonicTree := .branch 86069600 d14 d17
private def d5 : MobiusHarmonicTree := .branch 167015103 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606720 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606784 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 42921466 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606848 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606912 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 42516950 d26 d27
private def d21 : MobiusHarmonicTree := .branch 85438416 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 606976 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607040 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 43946087 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607104 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607168 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 45116131 d33 d34
private def d28 : MobiusHarmonicTree := .branch 89062218 d29 d32
private def d20 : MobiusHarmonicTree := .branch 174500634 d21 d28
private def d4 : MobiusHarmonicTree := .branch 341515737 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607232 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607296 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 45022578 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607360 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607424 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 44639512 d42 d43
private def d37 : MobiusHarmonicTree := .branch 89662090 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607488 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607552 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 39947331 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607616 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607680 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 41043055 d49 d50
private def d44 : MobiusHarmonicTree := .branch 80990386 d45 d48
private def d36 : MobiusHarmonicTree := .branch 170652476 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607744 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607808 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 41085470 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607872 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 607936 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 39724663 d57 d58
private def d52 : MobiusHarmonicTree := .branch 80810133 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608000 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608064 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 38561863 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608128 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608192 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 37363306 d64 d65
private def d59 : MobiusHarmonicTree := .branch 75925169 d60 d63
private def d51 : MobiusHarmonicTree := .branch 156735302 d52 d59
private def d35 : MobiusHarmonicTree := .branch 327387778 d36 d51
private def d3 : MobiusHarmonicTree := .branch 668903515 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608256 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608320 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 37920896 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608384 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608448 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 40258259 d74 d75
private def d69 : MobiusHarmonicTree := .branch 78179155 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608512 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608576 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 38772588 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608640 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608704 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 38593575 d81 d82
private def d76 : MobiusHarmonicTree := .branch 77366163 d77 d80
private def d68 : MobiusHarmonicTree := .branch 155545318 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608768 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608832 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 37700166 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608896 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 608960 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 39106119 d89 d90
private def d84 : MobiusHarmonicTree := .branch 76806285 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609024 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609088 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 39534579 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609152 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609216 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 43902353 d96 d97
private def d91 : MobiusHarmonicTree := .branch 83436932 d92 d95
private def d83 : MobiusHarmonicTree := .branch 160243217 d84 d91
private def d67 : MobiusHarmonicTree := .branch 315788535 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609280 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609344 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 47024350 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609408 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609472 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 49569253 d105 d106
private def d100 : MobiusHarmonicTree := .branch 96593603 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609536 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609600 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 50935104 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609664 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609728 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 50335703 d112 d113
private def d107 : MobiusHarmonicTree := .branch 101270807 d108 d111
private def d99 : MobiusHarmonicTree := .branch 197864410 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609792 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609856 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 47501523 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609920 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 609984 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 46166942 d120 d121
private def d115 : MobiusHarmonicTree := .branch 93668465 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610048 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610112 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 43801900 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610176 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610240 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 42901274 d127 d128
private def d122 : MobiusHarmonicTree := .branch 86703174 d123 d126
private def d114 : MobiusHarmonicTree := .branch 180371639 d115 d122
private def d98 : MobiusHarmonicTree := .branch 378236049 d99 d114
private def d66 : MobiusHarmonicTree := .branch 694024584 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1362928099 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610304 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610368 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 42594107 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610432 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610496 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 42395102 d138 d139
private def d133 : MobiusHarmonicTree := .branch 84989209 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610560 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610624 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 46021806 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610688 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610752 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 44857948 d145 d146
private def d140 : MobiusHarmonicTree := .branch 90879754 d141 d144
private def d132 : MobiusHarmonicTree := .branch 175868963 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610816 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610880 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 44625888 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 610944 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611008 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 42963535 d153 d154
private def d148 : MobiusHarmonicTree := .branch 87589423 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611072 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611136 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 44425546 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611200 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611264 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 45489420 d160 d161
private def d155 : MobiusHarmonicTree := .branch 89914966 d156 d159
private def d147 : MobiusHarmonicTree := .branch 177504389 d148 d155
private def d131 : MobiusHarmonicTree := .branch 353373352 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611328 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611392 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 44946678 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611456 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611520 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 45192441 d169 d170
private def d164 : MobiusHarmonicTree := .branch 90139119 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611584 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611648 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 43790004 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611712 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611776 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 41454807 d176 d177
private def d171 : MobiusHarmonicTree := .branch 85244811 d172 d175
private def d163 : MobiusHarmonicTree := .branch 175383930 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611840 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611904 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 41784445 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 611968 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612032 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 41649872 d184 d185
private def d179 : MobiusHarmonicTree := .branch 83434317 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612096 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612160 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 42977403 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612224 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612288 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 44217836 d191 d192
private def d186 : MobiusHarmonicTree := .branch 87195239 d187 d190
private def d178 : MobiusHarmonicTree := .branch 170629556 d179 d186
private def d162 : MobiusHarmonicTree := .branch 346013486 d163 d178
private def d130 : MobiusHarmonicTree := .branch 699386838 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612352 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612416 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 45776168 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612480 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612544 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 44387160 d201 d202
private def d196 : MobiusHarmonicTree := .branch 90163328 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612608 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612672 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 43948599 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612736 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612800 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 42304306 d208 d209
private def d203 : MobiusHarmonicTree := .branch 86252905 d204 d207
private def d195 : MobiusHarmonicTree := .branch 176416233 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612864 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612928 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 41536798 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 612992 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613056 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 41055128 d216 d217
private def d211 : MobiusHarmonicTree := .branch 82591926 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613120 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613184 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 41896036 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613248 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613312 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 46022348 d223 d224
private def d218 : MobiusHarmonicTree := .branch 87918384 d219 d222
private def d210 : MobiusHarmonicTree := .branch 170510310 d211 d218
private def d194 : MobiusHarmonicTree := .branch 346926543 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613376 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613440 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 47036469 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613504 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613568 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 46462790 d232 d233
private def d227 : MobiusHarmonicTree := .branch 93499259 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613632 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613696 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 44569431 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613760 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613824 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 43892152 d239 d240
private def d234 : MobiusHarmonicTree := .branch 88461583 d235 d238
private def d226 : MobiusHarmonicTree := .branch 181960842 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613888 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 613952 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 44677823 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614016 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614080 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 46653613 d247 d248
private def d242 : MobiusHarmonicTree := .branch 91331436 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614144 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614208 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 47453121 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614272 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock074 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614336 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 45711317 d254 d255
private def d249 : MobiusHarmonicTree := .branch 93164438 d250 d253
private def d241 : MobiusHarmonicTree := .branch 184495874 d242 d249
private def d225 : MobiusHarmonicTree := .branch 366456716 d226 d241
private def d193 : MobiusHarmonicTree := .branch 713383259 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1412770097 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2775698196 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614400 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614464 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 44101936 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614528 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614592 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 43389863 d266 d267
private def d261 : MobiusHarmonicTree := .branch 87491799 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614656 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614720 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 44864416 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614784 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614848 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 43331167 d273 d274
private def d268 : MobiusHarmonicTree := .branch 88195583 d269 d272
private def d260 : MobiusHarmonicTree := .branch 175687382 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614912 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 614976 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 43953017 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615040 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615104 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 42612470 d281 d282
private def d276 : MobiusHarmonicTree := .branch 86565487 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615168 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615232 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 40872475 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615296 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615360 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 41208471 d288 d289
private def d283 : MobiusHarmonicTree := .branch 82080946 d284 d287
private def d275 : MobiusHarmonicTree := .branch 168646433 d276 d283
private def d259 : MobiusHarmonicTree := .branch 344333815 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615424 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615488 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 41230774 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615552 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615616 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 43130847 d297 d298
private def d292 : MobiusHarmonicTree := .branch 84361621 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615680 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615744 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 44370818 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615808 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615872 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 45293572 d304 d305
private def d299 : MobiusHarmonicTree := .branch 89664390 d300 d303
private def d291 : MobiusHarmonicTree := .branch 174026011 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 615936 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616000 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 45175467 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616064 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616128 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 43833481 d312 d313
private def d307 : MobiusHarmonicTree := .branch 89008948 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616192 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616256 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 43151041 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616320 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616384 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 43907750 d319 d320
private def d314 : MobiusHarmonicTree := .branch 87058791 d315 d318
private def d306 : MobiusHarmonicTree := .branch 176067739 d307 d314
private def d290 : MobiusHarmonicTree := .branch 350093750 d291 d306
private def d258 : MobiusHarmonicTree := .branch 694427565 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616448 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616512 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 44326887 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616576 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616640 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 42918244 d329 d330
private def d324 : MobiusHarmonicTree := .branch 87245131 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616704 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616768 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 42880035 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616832 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616896 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 45623654 d336 d337
private def d331 : MobiusHarmonicTree := .branch 88503689 d332 d335
private def d323 : MobiusHarmonicTree := .branch 175748820 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 616960 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617024 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 45939946 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617088 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617152 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 48206983 d344 d345
private def d339 : MobiusHarmonicTree := .branch 94146929 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617216 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617280 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 51505030 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617344 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617408 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 53201529 d351 d352
private def d346 : MobiusHarmonicTree := .branch 104706559 d347 d350
private def d338 : MobiusHarmonicTree := .branch 198853488 d339 d346
private def d322 : MobiusHarmonicTree := .branch 374602308 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617472 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617536 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 54510266 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617600 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617664 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 53312295 d360 d361
private def d355 : MobiusHarmonicTree := .branch 107822561 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617728 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617792 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 53403210 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617856 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617920 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 52937344 d367 d368
private def d362 : MobiusHarmonicTree := .branch 106340554 d363 d366
private def d354 : MobiusHarmonicTree := .branch 214163115 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 617984 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618048 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 51952434 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618112 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618176 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 49720611 d375 d376
private def d370 : MobiusHarmonicTree := .branch 101673045 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618240 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618304 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 48429344 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618368 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618432 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 49695079 d382 d383
private def d377 : MobiusHarmonicTree := .branch 98124423 d378 d381
private def d369 : MobiusHarmonicTree := .branch 199797468 d370 d377
private def d353 : MobiusHarmonicTree := .branch 413960583 d354 d369
private def d321 : MobiusHarmonicTree := .branch 788562891 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1482990456 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618496 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618560 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 50040544 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618624 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618688 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 48132654 d393 d394
private def d388 : MobiusHarmonicTree := .branch 98173198 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618752 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618816 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 45575839 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618880 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 618944 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 45545435 d400 d401
private def d395 : MobiusHarmonicTree := .branch 91121274 d396 d399
private def d387 : MobiusHarmonicTree := .branch 189294472 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619008 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619072 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 46091702 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619136 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619200 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 44677097 d408 d409
private def d403 : MobiusHarmonicTree := .branch 90768799 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619264 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619328 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 44940746 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619392 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619456 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 43117023 d415 d416
private def d410 : MobiusHarmonicTree := .branch 88057769 d411 d414
private def d402 : MobiusHarmonicTree := .branch 178826568 d403 d410
private def d386 : MobiusHarmonicTree := .branch 368121040 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619520 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619584 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 42506028 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619648 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619712 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 40815856 d424 d425
private def d419 : MobiusHarmonicTree := .branch 83321884 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619776 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619840 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 41010643 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619904 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 619968 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 40895709 d431 d432
private def d426 : MobiusHarmonicTree := .branch 81906352 d427 d430
private def d418 : MobiusHarmonicTree := .branch 165228236 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620032 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620096 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 41908133 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620160 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620224 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 42784648 d439 d440
private def d434 : MobiusHarmonicTree := .branch 84692781 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620288 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620352 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 43348057 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620416 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620480 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 43856454 d446 d447
private def d441 : MobiusHarmonicTree := .branch 87204511 d442 d445
private def d433 : MobiusHarmonicTree := .branch 171897292 d434 d441
private def d417 : MobiusHarmonicTree := .branch 337125528 d418 d433
private def d385 : MobiusHarmonicTree := .branch 705246568 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620544 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620608 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 44442021 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620672 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620736 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 43909293 d456 d457
private def d451 : MobiusHarmonicTree := .branch 88351314 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620800 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620864 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 44431682 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620928 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 620992 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 45913705 d463 d464
private def d458 : MobiusHarmonicTree := .branch 90345387 d459 d462
private def d450 : MobiusHarmonicTree := .branch 178696701 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621056 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621120 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 46208598 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621184 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621248 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 46110519 d471 d472
private def d466 : MobiusHarmonicTree := .branch 92319117 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621312 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621376 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 46350461 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621440 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621504 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 45562223 d478 d479
private def d473 : MobiusHarmonicTree := .branch 91912684 d474 d477
private def d465 : MobiusHarmonicTree := .branch 184231801 d466 d473
private def d449 : MobiusHarmonicTree := .branch 362928502 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621568 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621632 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 40968102 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621696 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621760 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 38931584 d487 d488
private def d482 : MobiusHarmonicTree := .branch 79899686 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621824 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621888 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 37969922 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 621952 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622016 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 36835192 d494 d495
private def d489 : MobiusHarmonicTree := .branch 74805114 d490 d493
private def d481 : MobiusHarmonicTree := .branch 154704800 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622080 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622144 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 37301720 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622208 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622272 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 38624666 d502 d503
private def d497 : MobiusHarmonicTree := .branch 75926386 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622336 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622400 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 37932383 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622464 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock075 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 622528 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 34504556 d509 d510
private def d504 : MobiusHarmonicTree := .branch 72436939 d505 d508
private def d496 : MobiusHarmonicTree := .branch 148363325 d497 d504
private def d480 : MobiusHarmonicTree := .branch 303068125 d481 d496
private def d448 : MobiusHarmonicTree := .branch 665996627 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1371243195 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2854233651 d257 d384
private def d0 : MobiusHarmonicTree := .branch 5629931847 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 606208 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 606208 5629931847 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 606208 2775698196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 606208 1362928099 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 606208 668903515 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 606208 341515737 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 606208 167015103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 606208 80945503 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 606208 40816776 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 606336 40128727 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 606464 86069600 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 606464 43239639 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 606592 42829961 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 606720 174500634 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 606720 85438416 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 606720 42921466 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 606848 42516950 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 606976 89062218 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 606976 43946087 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 607104 45116131 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 607232 327387778 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 607232 170652476 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 607232 89662090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 607232 45022578 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 607360 44639512 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 607488 80990386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 607488 39947331 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 607616 41043055 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 607744 156735302 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 607744 80810133 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 607744 41085470 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 607872 39724663 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 608000 75925169 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 608000 38561863 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 608128 37363306 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 608256 694024584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 608256 315788535 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 608256 155545318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 608256 78179155 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 608256 37920896 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 608384 40258259 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 608512 77366163 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 608512 38772588 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 608640 38593575 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 608768 160243217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 608768 76806285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 608768 37700166 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 608896 39106119 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 609024 83436932 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 609024 39534579 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 609152 43902353 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 609280 378236049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 609280 197864410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 609280 96593603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 609280 47024350 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 609408 49569253 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 609536 101270807 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 609536 50935104 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 609664 50335703 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 609792 180371639 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 609792 93668465 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 609792 47501523 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 609920 46166942 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 610048 86703174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 610048 43801900 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 610176 42901274 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 610304 1412770097 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 610304 699386838 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 610304 353373352 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 610304 175868963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 610304 84989209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 610304 42594107 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 610432 42395102 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 610560 90879754 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 610560 46021806 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 610688 44857948 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 610816 177504389 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 610816 87589423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 610816 44625888 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 610944 42963535 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 611072 89914966 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 611072 44425546 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 611200 45489420 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 611328 346013486 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 611328 175383930 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 611328 90139119 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 611328 44946678 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 611456 45192441 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 611584 85244811 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 611584 43790004 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 611712 41454807 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 611840 170629556 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 611840 83434317 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 611840 41784445 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 611968 41649872 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 612096 87195239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 612096 42977403 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 612224 44217836 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 612352 713383259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 612352 346926543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 612352 176416233 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 612352 90163328 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 612352 45776168 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 612480 44387160 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 612608 86252905 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 612608 43948599 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 612736 42304306 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 612864 170510310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 612864 82591926 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 612864 41536798 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 612992 41055128 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 613120 87918384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 613120 41896036 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 613248 46022348 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 613376 366456716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 613376 181960842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 613376 93499259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 613376 47036469 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 613504 46462790 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 613632 88461583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 613632 44569431 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 613760 43892152 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 613888 184495874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 613888 91331436 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 613888 44677823 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 614016 46653613 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 614144 93164438 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 614144 47453121 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 614272 45711317 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 614400 2854233651 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 614400 1482990456 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 614400 694427565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 614400 344333815 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 614400 175687382 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 614400 87491799 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 614400 44101936 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 614528 43389863 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 614656 88195583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 614656 44864416 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 614784 43331167 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 614912 168646433 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 614912 86565487 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 614912 43953017 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 615040 42612470 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 615168 82080946 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 615168 40872475 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 615296 41208471 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 615424 350093750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 615424 174026011 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 615424 84361621 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 615424 41230774 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 615552 43130847 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 615680 89664390 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 615680 44370818 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 615808 45293572 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 615936 176067739 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 615936 89008948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 615936 45175467 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 616064 43833481 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 616192 87058791 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 616192 43151041 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 616320 43907750 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 616448 788562891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 616448 374602308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 616448 175748820 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 616448 87245131 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 616448 44326887 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 616576 42918244 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 616704 88503689 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 616704 42880035 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 616832 45623654 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 616960 198853488 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 616960 94146929 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 616960 45939946 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 617088 48206983 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 617216 104706559 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 617216 51505030 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 617344 53201529 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 617472 413960583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 617472 214163115 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 617472 107822561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 617472 54510266 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 617600 53312295 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 617728 106340554 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 617728 53403210 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 617856 52937344 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 617984 199797468 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 617984 101673045 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 617984 51952434 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 618112 49720611 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 618240 98124423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 618240 48429344 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 618368 49695079 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 618496 1371243195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 618496 705246568 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 618496 368121040 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 618496 189294472 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 618496 98173198 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 618496 50040544 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 618624 48132654 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 618752 91121274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 618752 45575839 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 618880 45545435 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 619008 178826568 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 619008 90768799 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 619008 46091702 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 619136 44677097 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 619264 88057769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 619264 44940746 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 619392 43117023 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 619520 337125528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 619520 165228236 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 619520 83321884 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 619520 42506028 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 619648 40815856 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 619776 81906352 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 619776 41010643 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 619904 40895709 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 620032 171897292 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 620032 84692781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 620032 41908133 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 620160 42784648 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 620288 87204511 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 620288 43348057 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 620416 43856454 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 620544 665996627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 620544 362928502 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 620544 178696701 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 620544 88351314 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 620544 44442021 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 620672 43909293 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 620800 90345387 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 620800 44431682 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 620928 45913705 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 621056 184231801 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 621056 92319117 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 621056 46208598 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 621184 46110519 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 621312 91912684 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 621312 46350461 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 621440 45562223 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 621568 303068125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 621568 154704800 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 621568 79899686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 621568 40968102 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 621696 38931584 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 621824 74805114 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 621824 37969922 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 621952 36835192 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 622080 148363325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 622080 75926386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 622080 37301720 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 622208 38624666 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 622336 72436939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 622336 37932383 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 622464 34504556 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 606208 (MobiusHarmonicTree.branch 5629931847 mobiusHarmonicBlock074 mobiusHarmonicBlock075) = true := Helfgott.combined

#print axioms solution
