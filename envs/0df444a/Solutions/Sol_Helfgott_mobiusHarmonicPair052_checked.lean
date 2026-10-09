-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair052_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:05:44.776021+00:00
-- url     : https://prove2.me/submissions/3abc4481-d373-4460-9749-365cbda41b35

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851968 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852032 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 24327825 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852096 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852160 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 24087111 d11 d12
private def d6 : MobiusHarmonicTree := .branch 48414936 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852224 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852288 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 24897755 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852352 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852416 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 25260022 d18 d19
private def d13 : MobiusHarmonicTree := .branch 50157777 d14 d17
private def d5 : MobiusHarmonicTree := .branch 98572713 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852480 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852544 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 24877385 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852608 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852672 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 26180143 d26 d27
private def d21 : MobiusHarmonicTree := .branch 51057528 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852736 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852800 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 25333124 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852864 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852928 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 25906115 d33 d34
private def d28 : MobiusHarmonicTree := .branch 51239239 d29 d32
private def d20 : MobiusHarmonicTree := .branch 102296767 d21 d28
private def d4 : MobiusHarmonicTree := .branch 200869480 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 852992 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853056 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 27519946 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853120 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853184 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 27479523 d42 d43
private def d37 : MobiusHarmonicTree := .branch 54999469 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853248 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853312 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 25661262 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853376 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853440 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 24106100 d49 d50
private def d44 : MobiusHarmonicTree := .branch 49767362 d45 d48
private def d36 : MobiusHarmonicTree := .branch 104766831 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853504 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853568 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 21624605 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853632 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853696 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 21720938 d57 d58
private def d52 : MobiusHarmonicTree := .branch 43345543 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853760 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853824 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 20711600 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853888 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 853952 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 20735425 d64 d65
private def d59 : MobiusHarmonicTree := .branch 41447025 d60 d63
private def d51 : MobiusHarmonicTree := .branch 84792568 d52 d59
private def d35 : MobiusHarmonicTree := .branch 189559399 d36 d51
private def d3 : MobiusHarmonicTree := .branch 390428879 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854016 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854080 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 20285071 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854144 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854208 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 18906513 d74 d75
private def d69 : MobiusHarmonicTree := .branch 39191584 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854272 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854336 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 18079598 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854400 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854464 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 18523975 d81 d82
private def d76 : MobiusHarmonicTree := .branch 36603573 d77 d80
private def d68 : MobiusHarmonicTree := .branch 75795157 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854528 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854592 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 17953648 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854656 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854720 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 17973231 d89 d90
private def d84 : MobiusHarmonicTree := .branch 35926879 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854784 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854848 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 16877947 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854912 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 854976 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 16137357 d96 d97
private def d91 : MobiusHarmonicTree := .branch 33015304 d92 d95
private def d83 : MobiusHarmonicTree := .branch 68942183 d84 d91
private def d67 : MobiusHarmonicTree := .branch 144737340 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855040 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855104 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 15393549 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855168 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855232 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 14644035 d105 d106
private def d100 : MobiusHarmonicTree := .branch 30037584 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855296 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855360 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 15423993 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855424 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855488 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 14730861 d112 d113
private def d107 : MobiusHarmonicTree := .branch 30154854 d108 d111
private def d99 : MobiusHarmonicTree := .branch 60192438 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855552 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855616 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 14874713 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855680 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855744 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 17466712 d120 d121
private def d115 : MobiusHarmonicTree := .branch 32341425 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855808 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855872 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 17709519 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 855936 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856000 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 16252420 d127 d128
private def d122 : MobiusHarmonicTree := .branch 33961939 d123 d126
private def d114 : MobiusHarmonicTree := .branch 66303364 d115 d122
private def d98 : MobiusHarmonicTree := .branch 126495802 d99 d114
private def d66 : MobiusHarmonicTree := .branch 271233142 d67 d98
private def d2 : MobiusHarmonicTree := .branch 661662021 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856064 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856128 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 16544318 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856192 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856256 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 17812505 d138 d139
private def d133 : MobiusHarmonicTree := .branch 34356823 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856320 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856384 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 17269205 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856448 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856512 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 17599333 d145 d146
private def d140 : MobiusHarmonicTree := .branch 34868538 d141 d144
private def d132 : MobiusHarmonicTree := .branch 69225361 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856576 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856640 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 18472264 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856704 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856768 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 18545357 d153 d154
private def d148 : MobiusHarmonicTree := .branch 37017621 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856832 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856896 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 18938194 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 856960 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857024 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 18875849 d160 d161
private def d155 : MobiusHarmonicTree := .branch 37814043 d156 d159
private def d147 : MobiusHarmonicTree := .branch 74831664 d148 d155
private def d131 : MobiusHarmonicTree := .branch 144057025 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857088 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857152 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 19368882 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857216 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857280 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 19192181 d169 d170
private def d164 : MobiusHarmonicTree := .branch 38561063 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857344 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857408 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 19338567 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857472 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857536 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 19537460 d176 d177
private def d171 : MobiusHarmonicTree := .branch 38876027 d172 d175
private def d163 : MobiusHarmonicTree := .branch 77437090 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857600 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857664 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 19142758 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857728 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857792 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 18973206 d184 d185
private def d179 : MobiusHarmonicTree := .branch 38115964 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857856 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857920 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 19282764 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 857984 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858048 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 18936096 d191 d192
private def d186 : MobiusHarmonicTree := .branch 38218860 d187 d190
private def d178 : MobiusHarmonicTree := .branch 76334824 d179 d186
private def d162 : MobiusHarmonicTree := .branch 153771914 d163 d178
private def d130 : MobiusHarmonicTree := .branch 297828939 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858112 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858176 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 19780411 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858240 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858304 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 18526163 d201 d202
private def d196 : MobiusHarmonicTree := .branch 38306574 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858368 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858432 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 17477307 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858496 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858560 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 16583669 d208 d209
private def d203 : MobiusHarmonicTree := .branch 34060976 d204 d207
private def d195 : MobiusHarmonicTree := .branch 72367550 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858624 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858688 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 16539257 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858752 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858816 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 16161865 d216 d217
private def d211 : MobiusHarmonicTree := .branch 32701122 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858880 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 858944 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 16564591 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859008 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859072 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 17175579 d223 d224
private def d218 : MobiusHarmonicTree := .branch 33740170 d219 d222
private def d210 : MobiusHarmonicTree := .branch 66441292 d211 d218
private def d194 : MobiusHarmonicTree := .branch 138808842 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859136 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859200 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 15876478 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859264 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859328 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 16004462 d232 d233
private def d227 : MobiusHarmonicTree := .branch 31880940 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859392 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859456 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 14463893 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859520 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859584 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 14159241 d239 d240
private def d234 : MobiusHarmonicTree := .branch 28623134 d235 d238
private def d226 : MobiusHarmonicTree := .branch 60504074 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859648 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859712 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 14778262 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859776 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859840 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 14857496 d247 d248
private def d242 : MobiusHarmonicTree := .branch 29635758 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859904 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 859968 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 13999420 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860032 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock104 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860096 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 13084673 d254 d255
private def d249 : MobiusHarmonicTree := .branch 27084093 d250 d253
private def d241 : MobiusHarmonicTree := .branch 56719851 d242 d249
private def d225 : MobiusHarmonicTree := .branch 117223925 d226 d241
private def d193 : MobiusHarmonicTree := .branch 256032767 d194 d225
private def d129 : MobiusHarmonicTree := .branch 553861706 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1215523727 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860160 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860224 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 12759551 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860288 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860352 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 12668143 d266 d267
private def d261 : MobiusHarmonicTree := .branch 25427694 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860416 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860480 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 13225234 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860544 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860608 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 12896771 d273 d274
private def d268 : MobiusHarmonicTree := .branch 26122005 d269 d272
private def d260 : MobiusHarmonicTree := .branch 51549699 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860672 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860736 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 14237841 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860800 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860864 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 17159550 d281 d282
private def d276 : MobiusHarmonicTree := .branch 31397391 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860928 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 860992 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 20410249 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861056 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861120 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 21178285 d288 d289
private def d283 : MobiusHarmonicTree := .branch 41588534 d284 d287
private def d275 : MobiusHarmonicTree := .branch 72985925 d276 d283
private def d259 : MobiusHarmonicTree := .branch 124535624 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861184 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861248 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 21363271 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861312 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861376 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 20885262 d297 d298
private def d292 : MobiusHarmonicTree := .branch 42248533 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861440 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861504 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 19242036 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861568 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861632 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 18460403 d304 d305
private def d299 : MobiusHarmonicTree := .branch 37702439 d300 d303
private def d291 : MobiusHarmonicTree := .branch 79950972 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861696 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861760 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 17322759 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861824 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861888 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 18104494 d312 d313
private def d307 : MobiusHarmonicTree := .branch 35427253 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 861952 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862016 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 18645899 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862080 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862144 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 18521335 d319 d320
private def d314 : MobiusHarmonicTree := .branch 37167234 d315 d318
private def d306 : MobiusHarmonicTree := .branch 72594487 d307 d314
private def d290 : MobiusHarmonicTree := .branch 152545459 d291 d306
private def d258 : MobiusHarmonicTree := .branch 277081083 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862208 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862272 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 20940064 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862336 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862400 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 22584689 d329 d330
private def d324 : MobiusHarmonicTree := .branch 43524753 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862464 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862528 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 22541972 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862592 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862656 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 21993792 d336 d337
private def d331 : MobiusHarmonicTree := .branch 44535764 d332 d335
private def d323 : MobiusHarmonicTree := .branch 88060517 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862720 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862784 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 22109898 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862848 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862912 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 21206159 d344 d345
private def d339 : MobiusHarmonicTree := .branch 43316057 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 862976 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863040 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 22701237 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863104 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863168 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 21882260 d351 d352
private def d346 : MobiusHarmonicTree := .branch 44583497 d347 d350
private def d338 : MobiusHarmonicTree := .branch 87899554 d339 d346
private def d322 : MobiusHarmonicTree := .branch 175960071 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863232 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863296 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 21772440 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863360 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863424 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 20577469 d360 d361
private def d355 : MobiusHarmonicTree := .branch 42349909 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863488 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863552 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 20936861 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863616 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863680 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 19855814 d367 d368
private def d362 : MobiusHarmonicTree := .branch 40792675 d363 d366
private def d354 : MobiusHarmonicTree := .branch 83142584 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863744 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863808 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 19385175 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863872 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 863936 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 19946000 d375 d376
private def d370 : MobiusHarmonicTree := .branch 39331175 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864000 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864064 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 20567996 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864128 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864192 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 21274277 d382 d383
private def d377 : MobiusHarmonicTree := .branch 41842273 d378 d381
private def d369 : MobiusHarmonicTree := .branch 81173448 d370 d377
private def d353 : MobiusHarmonicTree := .branch 164316032 d354 d369
private def d321 : MobiusHarmonicTree := .branch 340276103 d322 d353
private def d257 : MobiusHarmonicTree := .branch 617357186 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864256 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864320 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 20661438 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864384 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864448 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 20576189 d393 d394
private def d388 : MobiusHarmonicTree := .branch 41237627 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864512 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864576 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 20242395 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864640 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864704 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 18997351 d400 d401
private def d395 : MobiusHarmonicTree := .branch 39239746 d396 d399
private def d387 : MobiusHarmonicTree := .branch 80477373 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864768 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864832 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 16854239 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864896 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 864960 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 16052822 d408 d409
private def d403 : MobiusHarmonicTree := .branch 32907061 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865024 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865088 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 17186749 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865152 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865216 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 16197201 d415 d416
private def d410 : MobiusHarmonicTree := .branch 33383950 d411 d414
private def d402 : MobiusHarmonicTree := .branch 66291011 d403 d410
private def d386 : MobiusHarmonicTree := .branch 146768384 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865280 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865344 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 16446683 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865408 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865472 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 15852705 d424 d425
private def d419 : MobiusHarmonicTree := .branch 32299388 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865536 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865600 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 16490362 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865664 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865728 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 17331139 d431 d432
private def d426 : MobiusHarmonicTree := .branch 33821501 d427 d430
private def d418 : MobiusHarmonicTree := .branch 66120889 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865792 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865856 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 20661669 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865920 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 865984 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 20710642 d439 d440
private def d434 : MobiusHarmonicTree := .branch 41372311 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866048 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866112 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 20649829 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866176 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866240 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 20612136 d446 d447
private def d441 : MobiusHarmonicTree := .branch 41261965 d442 d445
private def d433 : MobiusHarmonicTree := .branch 82634276 d434 d441
private def d417 : MobiusHarmonicTree := .branch 148755165 d418 d433
private def d385 : MobiusHarmonicTree := .branch 295523549 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866304 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866368 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 20384036 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866432 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866496 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 19218899 d456 d457
private def d451 : MobiusHarmonicTree := .branch 39602935 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866560 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866624 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 17460935 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866688 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866752 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 18192125 d463 d464
private def d458 : MobiusHarmonicTree := .branch 35653060 d459 d462
private def d450 : MobiusHarmonicTree := .branch 75255995 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866816 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866880 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 18901170 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 866944 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867008 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 19362062 d471 d472
private def d466 : MobiusHarmonicTree := .branch 38263232 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867072 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867136 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 19561030 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867200 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867264 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 20778056 d478 d479
private def d473 : MobiusHarmonicTree := .branch 40339086 d474 d477
private def d465 : MobiusHarmonicTree := .branch 78602318 d466 d473
private def d449 : MobiusHarmonicTree := .branch 153858313 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867328 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867392 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 20705825 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867456 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867520 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 19122435 d487 d488
private def d482 : MobiusHarmonicTree := .branch 39828260 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867584 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867648 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 18075370 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867712 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867776 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 18236334 d494 d495
private def d489 : MobiusHarmonicTree := .branch 36311704 d490 d493
private def d481 : MobiusHarmonicTree := .branch 76139964 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867840 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867904 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 18407651 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 867968 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868032 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 18402624 d502 d503
private def d497 : MobiusHarmonicTree := .branch 36810275 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868096 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868160 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 18652162 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868224 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock105 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 868288 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 18761128 d509 d510
private def d504 : MobiusHarmonicTree := .branch 37413290 d505 d508
private def d496 : MobiusHarmonicTree := .branch 74223565 d497 d504
private def d480 : MobiusHarmonicTree := .branch 150363529 d481 d496
private def d448 : MobiusHarmonicTree := .branch 304221842 d449 d480
private def d384 : MobiusHarmonicTree := .branch 599745391 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1217102577 d257 d384
private def d0 : MobiusHarmonicTree := .branch 2432626304 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 851968 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 851968 2432626304 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 851968 1215523727 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 851968 661662021 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 851968 390428879 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 851968 200869480 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 851968 98572713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 851968 48414936 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 851968 24327825 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 852096 24087111 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 852224 50157777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 852224 24897755 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 852352 25260022 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 852480 102296767 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 852480 51057528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 852480 24877385 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 852608 26180143 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 852736 51239239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 852736 25333124 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 852864 25906115 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 852992 189559399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 852992 104766831 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 852992 54999469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 852992 27519946 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 853120 27479523 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 853248 49767362 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 853248 25661262 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 853376 24106100 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 853504 84792568 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 853504 43345543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 853504 21624605 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 853632 21720938 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 853760 41447025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 853760 20711600 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 853888 20735425 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 854016 271233142 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 854016 144737340 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 854016 75795157 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 854016 39191584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 854016 20285071 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 854144 18906513 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 854272 36603573 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 854272 18079598 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 854400 18523975 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 854528 68942183 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 854528 35926879 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 854528 17953648 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 854656 17973231 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 854784 33015304 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 854784 16877947 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 854912 16137357 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 855040 126495802 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 855040 60192438 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 855040 30037584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 855040 15393549 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 855168 14644035 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 855296 30154854 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 855296 15423993 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 855424 14730861 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 855552 66303364 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 855552 32341425 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 855552 14874713 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 855680 17466712 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 855808 33961939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 855808 17709519 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 855936 16252420 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 856064 553861706 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 856064 297828939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 856064 144057025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 856064 69225361 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 856064 34356823 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 856064 16544318 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 856192 17812505 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 856320 34868538 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 856320 17269205 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 856448 17599333 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 856576 74831664 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 856576 37017621 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 856576 18472264 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 856704 18545357 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 856832 37814043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 856832 18938194 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 856960 18875849 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 857088 153771914 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 857088 77437090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 857088 38561063 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 857088 19368882 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 857216 19192181 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 857344 38876027 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 857344 19338567 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 857472 19537460 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 857600 76334824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 857600 38115964 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 857600 19142758 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 857728 18973206 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 857856 38218860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 857856 19282764 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 857984 18936096 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 858112 256032767 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 858112 138808842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 858112 72367550 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 858112 38306574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 858112 19780411 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 858240 18526163 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 858368 34060976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 858368 17477307 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 858496 16583669 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 858624 66441292 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 858624 32701122 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 858624 16539257 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 858752 16161865 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 858880 33740170 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 858880 16564591 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 859008 17175579 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 859136 117223925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 859136 60504074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 859136 31880940 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 859136 15876478 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 859264 16004462 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 859392 28623134 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 859392 14463893 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 859520 14159241 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 859648 56719851 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 859648 29635758 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 859648 14778262 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 859776 14857496 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 859904 27084093 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 859904 13999420 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 860032 13084673 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 860160 1217102577 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 860160 617357186 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 860160 277081083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 860160 124535624 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 860160 51549699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 860160 25427694 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 860160 12759551 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 860288 12668143 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 860416 26122005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 860416 13225234 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 860544 12896771 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 860672 72985925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 860672 31397391 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 860672 14237841 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 860800 17159550 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 860928 41588534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 860928 20410249 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 861056 21178285 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 861184 152545459 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 861184 79950972 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 861184 42248533 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 861184 21363271 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 861312 20885262 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 861440 37702439 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 861440 19242036 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 861568 18460403 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 861696 72594487 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 861696 35427253 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 861696 17322759 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 861824 18104494 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 861952 37167234 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 861952 18645899 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 862080 18521335 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 862208 340276103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 862208 175960071 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 862208 88060517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 862208 43524753 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 862208 20940064 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 862336 22584689 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 862464 44535764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 862464 22541972 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 862592 21993792 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 862720 87899554 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 862720 43316057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 862720 22109898 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 862848 21206159 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 862976 44583497 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 862976 22701237 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 863104 21882260 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 863232 164316032 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 863232 83142584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 863232 42349909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 863232 21772440 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 863360 20577469 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 863488 40792675 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 863488 20936861 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 863616 19855814 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 863744 81173448 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 863744 39331175 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 863744 19385175 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 863872 19946000 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 864000 41842273 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 864000 20567996 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 864128 21274277 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 864256 599745391 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 864256 295523549 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 864256 146768384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 864256 80477373 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 864256 41237627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 864256 20661438 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 864384 20576189 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 864512 39239746 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 864512 20242395 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 864640 18997351 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 864768 66291011 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 864768 32907061 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 864768 16854239 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 864896 16052822 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 865024 33383950 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 865024 17186749 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 865152 16197201 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 865280 148755165 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 865280 66120889 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 865280 32299388 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 865280 16446683 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 865408 15852705 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 865536 33821501 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 865536 16490362 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 865664 17331139 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 865792 82634276 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 865792 41372311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 865792 20661669 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 865920 20710642 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 866048 41261965 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 866048 20649829 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 866176 20612136 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 866304 304221842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 866304 153858313 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 866304 75255995 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 866304 39602935 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 866304 20384036 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 866432 19218899 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 866560 35653060 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 866560 17460935 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 866688 18192125 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 866816 78602318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 866816 38263232 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 866816 18901170 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 866944 19362062 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 867072 40339086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 867072 19561030 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 867200 20778056 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 867328 150363529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 867328 76139964 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 867328 39828260 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 867328 20705825 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 867456 19122435 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 867584 36311704 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 867584 18075370 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 867712 18236334 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 867840 74223565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 867840 36810275 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 867840 18407651 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 867968 18402624 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 868096 37413290 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 868096 18652162 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 868224 18761128 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 851968 (MobiusHarmonicTree.branch 2432626304 mobiusHarmonicBlock104 mobiusHarmonicBlock105) = true := Helfgott.combined

#print axioms solution
