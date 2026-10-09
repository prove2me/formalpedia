-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair031_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:49:27.351485+00:00
-- url     : https://prove2.me/submissions/90e1062d-8a5b-4cbf-a974-8a740089b664

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507904 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 507968 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 18532809 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508032 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508096 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 14459938 d11 d12
private def d6 : MobiusHarmonicTree := .branch 32992747 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508160 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508224 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 16433737 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508288 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508352 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 19077335 d18 d19
private def d13 : MobiusHarmonicTree := .branch 35511072 d14 d17
private def d5 : MobiusHarmonicTree := .branch 68503819 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508416 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508480 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 18840552 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508544 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508608 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 17630610 d26 d27
private def d21 : MobiusHarmonicTree := .branch 36471162 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508672 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508736 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 18612921 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508800 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508864 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 18002969 d33 d34
private def d28 : MobiusHarmonicTree := .branch 36615890 d29 d32
private def d20 : MobiusHarmonicTree := .branch 73087052 d21 d28
private def d4 : MobiusHarmonicTree := .branch 141590871 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508928 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 508992 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 17509229 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509056 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509120 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 15980535 d42 d43
private def d37 : MobiusHarmonicTree := .branch 33489764 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509184 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509248 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 16589254 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509312 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509376 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 13534355 d49 d50
private def d44 : MobiusHarmonicTree := .branch 30123609 d45 d48
private def d36 : MobiusHarmonicTree := .branch 63613373 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509440 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509504 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 11864576 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509568 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509632 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 13335180 d57 d58
private def d52 : MobiusHarmonicTree := .branch 25199756 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509696 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509760 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 15574046 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509824 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509888 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 14605231 d64 d65
private def d59 : MobiusHarmonicTree := .branch 30179277 d60 d63
private def d51 : MobiusHarmonicTree := .branch 55379033 d52 d59
private def d35 : MobiusHarmonicTree := .branch 118992406 d36 d51
private def d3 : MobiusHarmonicTree := .branch 260583277 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 509952 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510016 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 13578125 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510080 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510144 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 11198947 d74 d75
private def d69 : MobiusHarmonicTree := .branch 24777072 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510208 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510272 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 10759063 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510336 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510400 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 8393590 d81 d82
private def d76 : MobiusHarmonicTree := .branch 19152653 d77 d80
private def d68 : MobiusHarmonicTree := .branch 43929725 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510464 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510528 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 6887069 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510592 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510656 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 7302491 d89 d90
private def d84 : MobiusHarmonicTree := .branch 14189560 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510720 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510784 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 4506910 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510848 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510912 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 2307731 d96 d97
private def d91 : MobiusHarmonicTree := .branch 6814641 d92 d95
private def d83 : MobiusHarmonicTree := .branch 21004201 d84 d91
private def d67 : MobiusHarmonicTree := .branch 64933926 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 510976 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511040 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 397269 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511104 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511168 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 1504498 d105 d106
private def d100 : MobiusHarmonicTree := .branch 1901767 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511232 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511296 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 334476 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511360 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511424 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 811482 d112 d113
private def d107 : MobiusHarmonicTree := .branch 1145958 d108 d111
private def d99 : MobiusHarmonicTree := .branch 3047725 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511488 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511552 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 848424 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511616 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511680 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 899037 d120 d121
private def d115 : MobiusHarmonicTree := .branch 1747461 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511744 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511808 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 1885492 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511872 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 511936 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 1316647 d127 d128
private def d122 : MobiusHarmonicTree := .branch 3202139 d123 d126
private def d114 : MobiusHarmonicTree := .branch 4949600 d115 d122
private def d98 : MobiusHarmonicTree := .branch 7997325 d99 d114
private def d66 : MobiusHarmonicTree := .branch 72931251 d67 d98
private def d2 : MobiusHarmonicTree := .branch 333514528 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512000 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512064 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 1402203 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512128 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512192 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 1599089 d138 d139
private def d133 : MobiusHarmonicTree := .branch 3001292 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512256 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512320 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 2847903 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512384 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512448 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 3387718 d145 d146
private def d140 : MobiusHarmonicTree := .branch 6235621 d141 d144
private def d132 : MobiusHarmonicTree := .branch 9236913 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512512 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512576 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 2614415 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512640 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512704 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 448672 d153 d154
private def d148 : MobiusHarmonicTree := .branch 3063087 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512768 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512832 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 1029615 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512896 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512960 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 2423279 d160 d161
private def d155 : MobiusHarmonicTree := .branch 3452894 d156 d159
private def d147 : MobiusHarmonicTree := .branch 6515981 d148 d155
private def d131 : MobiusHarmonicTree := .branch 15752894 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513024 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513088 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 1089559 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513152 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513216 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 1034719 d169 d170
private def d164 : MobiusHarmonicTree := .branch 2124278 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513280 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513344 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 489008 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513408 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513472 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 2911572 d176 d177
private def d171 : MobiusHarmonicTree := .branch 3400580 d172 d175
private def d163 : MobiusHarmonicTree := .branch 5524858 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513536 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513600 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 3364543 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513664 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513728 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 5619685 d184 d185
private def d179 : MobiusHarmonicTree := .branch 8984228 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513792 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513856 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 7204378 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513920 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 513984 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 9932244 d191 d192
private def d186 : MobiusHarmonicTree := .branch 17136622 d187 d190
private def d178 : MobiusHarmonicTree := .branch 26120850 d179 d186
private def d162 : MobiusHarmonicTree := .branch 31645708 d163 d178
private def d130 : MobiusHarmonicTree := .branch 47398602 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514048 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514112 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 10505549 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514176 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514240 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 11319639 d201 d202
private def d196 : MobiusHarmonicTree := .branch 21825188 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514304 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514368 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 10578171 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514432 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514496 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 9366478 d208 d209
private def d203 : MobiusHarmonicTree := .branch 19944649 d204 d207
private def d195 : MobiusHarmonicTree := .branch 41769837 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514560 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514624 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 6165799 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514688 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514752 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 5940750 d216 d217
private def d211 : MobiusHarmonicTree := .branch 12106549 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514816 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514880 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 8411701 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 514944 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515008 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 5928270 d223 d224
private def d218 : MobiusHarmonicTree := .branch 14339971 d219 d222
private def d210 : MobiusHarmonicTree := .branch 26446520 d211 d218
private def d194 : MobiusHarmonicTree := .branch 68216357 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515072 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515136 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 2251943 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515200 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515264 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 1849570 d232 d233
private def d227 : MobiusHarmonicTree := .branch 4101513 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515328 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515392 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 2246901 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515456 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515520 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 1191065 d239 d240
private def d234 : MobiusHarmonicTree := .branch 3437966 d235 d238
private def d226 : MobiusHarmonicTree := .branch 7539479 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515584 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515648 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 2788741 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515712 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515776 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 3270829 d247 d248
private def d242 : MobiusHarmonicTree := .branch 6059570 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515840 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515904 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 5125031 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 515968 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock062 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516032 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 3887474 d254 d255
private def d249 : MobiusHarmonicTree := .branch 9012505 d250 d253
private def d241 : MobiusHarmonicTree := .branch 15072075 d242 d249
private def d225 : MobiusHarmonicTree := .branch 22611554 d226 d241
private def d193 : MobiusHarmonicTree := .branch 90827911 d194 d225
private def d129 : MobiusHarmonicTree := .branch 138226513 d130 d193
private def d1 : MobiusHarmonicTree := .branch 471741041 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516096 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516160 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 4444367 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516224 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516288 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 5593848 d266 d267
private def d261 : MobiusHarmonicTree := .branch 10038215 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516352 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516416 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 6638087 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516480 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516544 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 8839484 d273 d274
private def d268 : MobiusHarmonicTree := .branch 15477571 d269 d272
private def d260 : MobiusHarmonicTree := .branch 25515786 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516608 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516672 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 12296028 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516736 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516800 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 14847171 d281 d282
private def d276 : MobiusHarmonicTree := .branch 27143199 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516864 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516928 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 16710360 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 516992 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517056 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 16858963 d288 d289
private def d283 : MobiusHarmonicTree := .branch 33569323 d284 d287
private def d275 : MobiusHarmonicTree := .branch 60712522 d276 d283
private def d259 : MobiusHarmonicTree := .branch 86228308 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517120 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517184 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 17999442 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517248 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517312 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 20685836 d297 d298
private def d292 : MobiusHarmonicTree := .branch 38685278 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517376 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517440 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 21876963 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517504 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517568 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 24501187 d304 d305
private def d299 : MobiusHarmonicTree := .branch 46378150 d300 d303
private def d291 : MobiusHarmonicTree := .branch 85063428 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517632 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517696 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 24471975 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517760 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517824 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 23407625 d312 d313
private def d307 : MobiusHarmonicTree := .branch 47879600 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517888 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 517952 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 24566095 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518016 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518080 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 25328182 d319 d320
private def d314 : MobiusHarmonicTree := .branch 49894277 d315 d318
private def d306 : MobiusHarmonicTree := .branch 97773877 d307 d314
private def d290 : MobiusHarmonicTree := .branch 182837305 d291 d306
private def d258 : MobiusHarmonicTree := .branch 269065613 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518144 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518208 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 29142742 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518272 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518336 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 28925396 d329 d330
private def d324 : MobiusHarmonicTree := .branch 58068138 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518400 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518464 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 26123418 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518528 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518592 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 25602121 d336 d337
private def d331 : MobiusHarmonicTree := .branch 51725539 d332 d335
private def d323 : MobiusHarmonicTree := .branch 109793677 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518656 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518720 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 26773589 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518784 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518848 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 29600196 d344 d345
private def d339 : MobiusHarmonicTree := .branch 56373785 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518912 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 518976 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 29855066 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519040 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519104 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 31311711 d351 d352
private def d346 : MobiusHarmonicTree := .branch 61166777 d347 d350
private def d338 : MobiusHarmonicTree := .branch 117540562 d339 d346
private def d322 : MobiusHarmonicTree := .branch 227334239 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519168 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519232 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 31140298 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519296 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519360 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 32451516 d360 d361
private def d355 : MobiusHarmonicTree := .branch 63591814 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519424 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519488 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 33715911 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519552 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519616 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 34662258 d367 d368
private def d362 : MobiusHarmonicTree := .branch 68378169 d363 d366
private def d354 : MobiusHarmonicTree := .branch 131969983 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519680 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519744 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 36208228 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519808 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519872 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 35156872 d375 d376
private def d370 : MobiusHarmonicTree := .branch 71365100 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 519936 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520000 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 32892481 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520064 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520128 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 32613210 d382 d383
private def d377 : MobiusHarmonicTree := .branch 65505691 d378 d381
private def d369 : MobiusHarmonicTree := .branch 136870791 d370 d377
private def d353 : MobiusHarmonicTree := .branch 268840774 d354 d369
private def d321 : MobiusHarmonicTree := .branch 496175013 d322 d353
private def d257 : MobiusHarmonicTree := .branch 765240626 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520192 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520256 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 31646071 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520320 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520384 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 34257445 d393 d394
private def d388 : MobiusHarmonicTree := .branch 65903516 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520448 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520512 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 33029163 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520576 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520640 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 33159302 d400 d401
private def d395 : MobiusHarmonicTree := .branch 66188465 d396 d399
private def d387 : MobiusHarmonicTree := .branch 132091981 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520704 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520768 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 33525606 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520832 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520896 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 32058363 d408 d409
private def d403 : MobiusHarmonicTree := .branch 65583969 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 520960 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521024 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 32017796 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521088 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521152 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 31426600 d415 d416
private def d410 : MobiusHarmonicTree := .branch 63444396 d411 d414
private def d402 : MobiusHarmonicTree := .branch 129028365 d403 d410
private def d386 : MobiusHarmonicTree := .branch 261120346 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521216 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521280 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 32821150 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521344 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521408 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 34107752 d424 d425
private def d419 : MobiusHarmonicTree := .branch 66928902 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521472 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521536 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 32657458 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521600 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521664 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 31315307 d431 d432
private def d426 : MobiusHarmonicTree := .branch 63972765 d427 d430
private def d418 : MobiusHarmonicTree := .branch 130901667 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521728 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521792 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 31035425 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521856 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521920 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 32445658 d439 d440
private def d434 : MobiusHarmonicTree := .branch 63481083 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 521984 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522048 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 32453073 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522112 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522176 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 30838339 d446 d447
private def d441 : MobiusHarmonicTree := .branch 63291412 d442 d445
private def d433 : MobiusHarmonicTree := .branch 126772495 d434 d441
private def d417 : MobiusHarmonicTree := .branch 257674162 d418 d433
private def d385 : MobiusHarmonicTree := .branch 518794508 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522240 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522304 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 33547579 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522368 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522432 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 34699356 d456 d457
private def d451 : MobiusHarmonicTree := .branch 68246935 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522496 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522560 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 35368252 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522624 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522688 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 36268369 d463 d464
private def d458 : MobiusHarmonicTree := .branch 71636621 d459 d462
private def d450 : MobiusHarmonicTree := .branch 139883556 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522752 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522816 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 37998114 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522880 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 522944 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 39465180 d471 d472
private def d466 : MobiusHarmonicTree := .branch 77463294 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523008 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523072 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 38528214 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523136 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523200 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 39157203 d478 d479
private def d473 : MobiusHarmonicTree := .branch 77685417 d474 d477
private def d465 : MobiusHarmonicTree := .branch 155148711 d466 d473
private def d449 : MobiusHarmonicTree := .branch 295032267 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523264 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523328 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 37502449 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523392 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523456 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 34199786 d487 d488
private def d482 : MobiusHarmonicTree := .branch 71702235 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523520 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523584 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 31162273 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523648 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523712 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 32109345 d494 d495
private def d489 : MobiusHarmonicTree := .branch 63271618 d490 d493
private def d481 : MobiusHarmonicTree := .branch 134973853 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523776 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523840 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 33015857 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523904 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 523968 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 32832341 d502 d503
private def d497 : MobiusHarmonicTree := .branch 65848198 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524032 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524096 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 31553500 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524160 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock063 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 524224 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 31437023 d509 d510
private def d504 : MobiusHarmonicTree := .branch 62990523 d505 d508
private def d496 : MobiusHarmonicTree := .branch 128838721 d497 d504
private def d480 : MobiusHarmonicTree := .branch 263812574 d481 d496
private def d448 : MobiusHarmonicTree := .branch 558844841 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1077639349 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1842879975 d257 d384
private def d0 : MobiusHarmonicTree := .branch 2314621016 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 507904 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 507904 2314621016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 507904 471741041 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 507904 333514528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 507904 260583277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 507904 141590871 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 507904 68503819 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 507904 32992747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 507904 18532809 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 508032 14459938 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 508160 35511072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 508160 16433737 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 508288 19077335 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 508416 73087052 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 508416 36471162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 508416 18840552 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 508544 17630610 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 508672 36615890 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 508672 18612921 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 508800 18002969 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 508928 118992406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 508928 63613373 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 508928 33489764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 508928 17509229 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 509056 15980535 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 509184 30123609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 509184 16589254 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 509312 13534355 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 509440 55379033 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 509440 25199756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 509440 11864576 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 509568 13335180 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 509696 30179277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 509696 15574046 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 509824 14605231 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 509952 72931251 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 509952 64933926 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 509952 43929725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 509952 24777072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 509952 13578125 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 510080 11198947 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 510208 19152653 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 510208 10759063 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 510336 8393590 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 510464 21004201 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 510464 14189560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 510464 6887069 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 510592 7302491 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 510720 6814641 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 510720 4506910 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 510848 2307731 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 510976 7997325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 510976 3047725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 510976 1901767 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 510976 397269 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 511104 1504498 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 511232 1145958 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 511232 334476 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 511360 811482 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 511488 4949600 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 511488 1747461 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 511488 848424 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 511616 899037 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 511744 3202139 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 511744 1885492 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 511872 1316647 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 512000 138226513 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 512000 47398602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 512000 15752894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 512000 9236913 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 512000 3001292 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 512000 1402203 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 512128 1599089 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 512256 6235621 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 512256 2847903 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 512384 3387718 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 512512 6515981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 512512 3063087 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 512512 2614415 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 512640 448672 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 512768 3452894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 512768 1029615 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 512896 2423279 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 513024 31645708 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 513024 5524858 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 513024 2124278 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 513024 1089559 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 513152 1034719 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 513280 3400580 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 513280 489008 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 513408 2911572 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 513536 26120850 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 513536 8984228 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 513536 3364543 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 513664 5619685 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 513792 17136622 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 513792 7204378 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 513920 9932244 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 514048 90827911 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 514048 68216357 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 514048 41769837 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 514048 21825188 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 514048 10505549 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 514176 11319639 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 514304 19944649 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 514304 10578171 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 514432 9366478 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 514560 26446520 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 514560 12106549 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 514560 6165799 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 514688 5940750 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 514816 14339971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 514816 8411701 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 514944 5928270 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 515072 22611554 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 515072 7539479 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 515072 4101513 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 515072 2251943 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 515200 1849570 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 515328 3437966 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 515328 2246901 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 515456 1191065 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 515584 15072075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 515584 6059570 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 515584 2788741 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 515712 3270829 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 515840 9012505 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 515840 5125031 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 515968 3887474 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 516096 1842879975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 516096 765240626 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 516096 269065613 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 516096 86228308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 516096 25515786 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 516096 10038215 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 516096 4444367 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 516224 5593848 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 516352 15477571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 516352 6638087 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 516480 8839484 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 516608 60712522 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 516608 27143199 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 516608 12296028 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 516736 14847171 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 516864 33569323 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 516864 16710360 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 516992 16858963 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 517120 182837305 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 517120 85063428 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 517120 38685278 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 517120 17999442 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 517248 20685836 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 517376 46378150 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 517376 21876963 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 517504 24501187 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 517632 97773877 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 517632 47879600 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 517632 24471975 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 517760 23407625 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 517888 49894277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 517888 24566095 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 518016 25328182 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 518144 496175013 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 518144 227334239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 518144 109793677 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 518144 58068138 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 518144 29142742 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 518272 28925396 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 518400 51725539 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 518400 26123418 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 518528 25602121 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 518656 117540562 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 518656 56373785 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 518656 26773589 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 518784 29600196 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 518912 61166777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 518912 29855066 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 519040 31311711 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 519168 268840774 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 519168 131969983 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 519168 63591814 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 519168 31140298 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 519296 32451516 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 519424 68378169 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 519424 33715911 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 519552 34662258 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 519680 136870791 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 519680 71365100 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 519680 36208228 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 519808 35156872 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 519936 65505691 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 519936 32892481 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 520064 32613210 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 520192 1077639349 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 520192 518794508 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 520192 261120346 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 520192 132091981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 520192 65903516 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 520192 31646071 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 520320 34257445 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 520448 66188465 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 520448 33029163 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 520576 33159302 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 520704 129028365 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 520704 65583969 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 520704 33525606 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 520832 32058363 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 520960 63444396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 520960 32017796 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 521088 31426600 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 521216 257674162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 521216 130901667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 521216 66928902 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 521216 32821150 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 521344 34107752 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 521472 63972765 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 521472 32657458 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 521600 31315307 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 521728 126772495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 521728 63481083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 521728 31035425 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 521856 32445658 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 521984 63291412 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 521984 32453073 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 522112 30838339 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 522240 558844841 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 522240 295032267 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 522240 139883556 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 522240 68246935 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 522240 33547579 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 522368 34699356 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 522496 71636621 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 522496 35368252 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 522624 36268369 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 522752 155148711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 522752 77463294 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 522752 37998114 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 522880 39465180 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 523008 77685417 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 523008 38528214 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 523136 39157203 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 523264 263812574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 523264 134973853 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 523264 71702235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 523264 37502449 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 523392 34199786 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 523520 63271618 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 523520 31162273 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 523648 32109345 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 523776 128838721 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 523776 65848198 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 523776 33015857 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 523904 32832341 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 524032 62990523 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 524032 31553500 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 524160 31437023 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 507904 (MobiusHarmonicTree.branch 2314621016 mobiusHarmonicBlock062 mobiusHarmonicBlock063) = true := Helfgott.combined

#print axioms solution
