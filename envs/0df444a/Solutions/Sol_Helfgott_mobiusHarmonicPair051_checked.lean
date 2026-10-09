-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair051_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:02:56.130019+00:00
-- url     : https://prove2.me/submissions/feef6a74-4738-4696-af2e-c83715f59247

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835584 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835648 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 24114276 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835712 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835776 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 25345359 d11 d12
private def d6 : MobiusHarmonicTree := .branch 49459635 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835840 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835904 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 26442136 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835968 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836032 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 25934475 d18 d19
private def d13 : MobiusHarmonicTree := .branch 52376611 d14 d17
private def d5 : MobiusHarmonicTree := .branch 101836246 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836096 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836160 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 27798547 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836224 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836288 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 29769727 d26 d27
private def d21 : MobiusHarmonicTree := .branch 57568274 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836352 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836416 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 29774752 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836480 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836544 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 27999839 d33 d34
private def d28 : MobiusHarmonicTree := .branch 57774591 d29 d32
private def d20 : MobiusHarmonicTree := .branch 115342865 d21 d28
private def d4 : MobiusHarmonicTree := .branch 217179111 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836608 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836672 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 26739360 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836736 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836800 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 27110489 d42 d43
private def d37 : MobiusHarmonicTree := .branch 53849849 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836864 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836928 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 26298638 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 836992 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837056 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 25976810 d49 d50
private def d44 : MobiusHarmonicTree := .branch 52275448 d45 d48
private def d36 : MobiusHarmonicTree := .branch 106125297 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837120 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837184 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 27186460 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837248 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837312 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 26116992 d57 d58
private def d52 : MobiusHarmonicTree := .branch 53303452 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837376 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837440 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 26022256 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837504 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837568 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 24893599 d64 d65
private def d59 : MobiusHarmonicTree := .branch 50915855 d60 d63
private def d51 : MobiusHarmonicTree := .branch 104219307 d52 d59
private def d35 : MobiusHarmonicTree := .branch 210344604 d36 d51
private def d3 : MobiusHarmonicTree := .branch 427523715 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837632 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837696 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 23368953 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837760 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837824 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 22831843 d74 d75
private def d69 : MobiusHarmonicTree := .branch 46200796 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837888 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 837952 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 22084877 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838016 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838080 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 22363094 d81 d82
private def d76 : MobiusHarmonicTree := .branch 44447971 d77 d80
private def d68 : MobiusHarmonicTree := .branch 90648767 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838144 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838208 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 22586359 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838272 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838336 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 20961872 d89 d90
private def d84 : MobiusHarmonicTree := .branch 43548231 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838400 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838464 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 21627695 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838528 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838592 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 23460813 d96 d97
private def d91 : MobiusHarmonicTree := .branch 45088508 d92 d95
private def d83 : MobiusHarmonicTree := .branch 88636739 d84 d91
private def d67 : MobiusHarmonicTree := .branch 179285506 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838656 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838720 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 23879335 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838784 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838848 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 22502399 d105 d106
private def d100 : MobiusHarmonicTree := .branch 46381734 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838912 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 838976 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 21746808 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839040 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839104 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 21828168 d112 d113
private def d107 : MobiusHarmonicTree := .branch 43574976 d108 d111
private def d99 : MobiusHarmonicTree := .branch 89956710 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839168 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839232 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 20485467 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839296 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839360 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 20783757 d120 d121
private def d115 : MobiusHarmonicTree := .branch 41269224 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839424 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839488 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 20990233 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839552 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839616 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 20248626 d127 d128
private def d122 : MobiusHarmonicTree := .branch 41238859 d123 d126
private def d114 : MobiusHarmonicTree := .branch 82508083 d115 d122
private def d98 : MobiusHarmonicTree := .branch 172464793 d99 d114
private def d66 : MobiusHarmonicTree := .branch 351750299 d67 d98
private def d2 : MobiusHarmonicTree := .branch 779274014 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839680 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839744 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 21991257 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839808 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839872 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 22752351 d138 d139
private def d133 : MobiusHarmonicTree := .branch 44743608 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 839936 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840000 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 23503642 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840064 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840128 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 23572667 d145 d146
private def d140 : MobiusHarmonicTree := .branch 47076309 d141 d144
private def d132 : MobiusHarmonicTree := .branch 91819917 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840192 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840256 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 24581851 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840320 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840384 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 25170732 d153 d154
private def d148 : MobiusHarmonicTree := .branch 49752583 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840448 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840512 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 24410207 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840576 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840640 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 23032552 d160 d161
private def d155 : MobiusHarmonicTree := .branch 47442759 d156 d159
private def d147 : MobiusHarmonicTree := .branch 97195342 d148 d155
private def d131 : MobiusHarmonicTree := .branch 189015259 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840704 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840768 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 22686482 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840832 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840896 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 22152659 d169 d170
private def d164 : MobiusHarmonicTree := .branch 44839141 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 840960 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841024 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 22118336 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841088 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841152 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 23372766 d176 d177
private def d171 : MobiusHarmonicTree := .branch 45491102 d172 d175
private def d163 : MobiusHarmonicTree := .branch 90330243 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841216 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841280 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 26727159 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841344 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841408 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 27771388 d184 d185
private def d179 : MobiusHarmonicTree := .branch 54498547 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841472 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841536 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 26229514 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841600 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841664 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 25328505 d191 d192
private def d186 : MobiusHarmonicTree := .branch 51558019 d187 d190
private def d178 : MobiusHarmonicTree := .branch 106056566 d179 d186
private def d162 : MobiusHarmonicTree := .branch 196386809 d163 d178
private def d130 : MobiusHarmonicTree := .branch 385402068 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841728 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841792 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 23044970 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841856 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841920 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 23497556 d201 d202
private def d196 : MobiusHarmonicTree := .branch 46542526 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 841984 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842048 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 23527234 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842112 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842176 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 24772772 d208 d209
private def d203 : MobiusHarmonicTree := .branch 48300006 d204 d207
private def d195 : MobiusHarmonicTree := .branch 94842532 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842240 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842304 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 26244763 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842368 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842432 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 28034358 d216 d217
private def d211 : MobiusHarmonicTree := .branch 54279121 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842496 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842560 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 30014584 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842624 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842688 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 28009290 d223 d224
private def d218 : MobiusHarmonicTree := .branch 58023874 d219 d222
private def d210 : MobiusHarmonicTree := .branch 112302995 d211 d218
private def d194 : MobiusHarmonicTree := .branch 207145527 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842752 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842816 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 27164966 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842880 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 842944 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 26753928 d232 d233
private def d227 : MobiusHarmonicTree := .branch 53918894 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843008 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843072 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 27806710 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843136 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843200 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 29863660 d239 d240
private def d234 : MobiusHarmonicTree := .branch 57670370 d235 d238
private def d226 : MobiusHarmonicTree := .branch 111589264 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843264 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843328 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 32097878 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843392 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843456 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 31895058 d247 d248
private def d242 : MobiusHarmonicTree := .branch 63992936 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843520 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843584 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 32162864 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843648 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock102 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843712 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 32219616 d254 d255
private def d249 : MobiusHarmonicTree := .branch 64382480 d250 d253
private def d241 : MobiusHarmonicTree := .branch 128375416 d242 d249
private def d225 : MobiusHarmonicTree := .branch 239964680 d226 d241
private def d193 : MobiusHarmonicTree := .branch 447110207 d194 d225
private def d129 : MobiusHarmonicTree := .branch 832512275 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1611786289 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843776 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843840 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 33236226 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843904 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 843968 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 33317723 d266 d267
private def d261 : MobiusHarmonicTree := .branch 66553949 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844032 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844096 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 33664464 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844160 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844224 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 35378127 d273 d274
private def d268 : MobiusHarmonicTree := .branch 69042591 d269 d272
private def d260 : MobiusHarmonicTree := .branch 135596540 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844288 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844352 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 35640425 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844416 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844480 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 37076154 d281 d282
private def d276 : MobiusHarmonicTree := .branch 72716579 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844544 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844608 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 36914238 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844672 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844736 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 38264097 d288 d289
private def d283 : MobiusHarmonicTree := .branch 75178335 d284 d287
private def d275 : MobiusHarmonicTree := .branch 147894914 d276 d283
private def d259 : MobiusHarmonicTree := .branch 283491454 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844800 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844864 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 38771993 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844928 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 844992 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 39343665 d297 d298
private def d292 : MobiusHarmonicTree := .branch 78115658 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845056 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845120 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 37742704 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845184 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845248 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 37398570 d304 d305
private def d299 : MobiusHarmonicTree := .branch 75141274 d300 d303
private def d291 : MobiusHarmonicTree := .branch 153256932 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845312 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845376 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 37903941 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845440 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845504 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 36829007 d312 d313
private def d307 : MobiusHarmonicTree := .branch 74732948 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845568 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845632 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 36466289 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845696 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845760 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 34832714 d319 d320
private def d314 : MobiusHarmonicTree := .branch 71299003 d315 d318
private def d306 : MobiusHarmonicTree := .branch 146031951 d307 d314
private def d290 : MobiusHarmonicTree := .branch 299288883 d291 d306
private def d258 : MobiusHarmonicTree := .branch 582780337 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845824 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845888 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 32843651 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 845952 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846016 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 33864720 d329 d330
private def d324 : MobiusHarmonicTree := .branch 66708371 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846080 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846144 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 31681487 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846208 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846272 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 29450439 d336 d337
private def d331 : MobiusHarmonicTree := .branch 61131926 d332 d335
private def d323 : MobiusHarmonicTree := .branch 127840297 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846336 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846400 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 28982828 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846464 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846528 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 27176993 d344 d345
private def d339 : MobiusHarmonicTree := .branch 56159821 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846592 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846656 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 25332680 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846720 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846784 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 24167990 d351 d352
private def d346 : MobiusHarmonicTree := .branch 49500670 d347 d350
private def d338 : MobiusHarmonicTree := .branch 105660491 d339 d346
private def d322 : MobiusHarmonicTree := .branch 233500788 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846848 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846912 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 23435811 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 846976 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847040 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 24380260 d360 d361
private def d355 : MobiusHarmonicTree := .branch 47816071 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847104 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847168 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 25114338 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847232 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847296 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 25229753 d367 d368
private def d362 : MobiusHarmonicTree := .branch 50344091 d363 d366
private def d354 : MobiusHarmonicTree := .branch 98160162 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847360 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847424 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 24985228 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847488 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847552 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 23569117 d375 d376
private def d370 : MobiusHarmonicTree := .branch 48554345 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847616 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847680 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 25221863 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847744 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847808 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 23386288 d382 d383
private def d377 : MobiusHarmonicTree := .branch 48608151 d378 d381
private def d369 : MobiusHarmonicTree := .branch 97162496 d370 d377
private def d353 : MobiusHarmonicTree := .branch 195322658 d354 d369
private def d321 : MobiusHarmonicTree := .branch 428823446 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1011603783 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847872 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 847936 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 24394575 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848000 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848064 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 23644562 d393 d394
private def d388 : MobiusHarmonicTree := .branch 48039137 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848128 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848192 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 23260149 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848256 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848320 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 22363131 d400 d401
private def d395 : MobiusHarmonicTree := .branch 45623280 d396 d399
private def d387 : MobiusHarmonicTree := .branch 93662417 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848384 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848448 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 21913011 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848512 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848576 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 22385805 d408 d409
private def d403 : MobiusHarmonicTree := .branch 44298816 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848640 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848704 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 22847858 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848768 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848832 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 22560504 d415 d416
private def d410 : MobiusHarmonicTree := .branch 45408362 d411 d414
private def d402 : MobiusHarmonicTree := .branch 89707178 d403 d410
private def d386 : MobiusHarmonicTree := .branch 183369595 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848896 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 848960 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 22130683 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849024 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849088 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 22225086 d424 d425
private def d419 : MobiusHarmonicTree := .branch 44355769 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849152 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849216 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 21915601 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849280 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849344 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 20664268 d431 d432
private def d426 : MobiusHarmonicTree := .branch 42579869 d427 d430
private def d418 : MobiusHarmonicTree := .branch 86935638 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849408 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849472 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 19262651 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849536 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849600 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 18367549 d439 d440
private def d434 : MobiusHarmonicTree := .branch 37630200 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849664 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849728 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 18511874 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849792 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849856 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 18735000 d446 d447
private def d441 : MobiusHarmonicTree := .branch 37246874 d442 d445
private def d433 : MobiusHarmonicTree := .branch 74877074 d434 d441
private def d417 : MobiusHarmonicTree := .branch 161812712 d418 d433
private def d385 : MobiusHarmonicTree := .branch 345182307 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849920 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 849984 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 19682781 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850048 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850112 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 21353744 d456 d457
private def d451 : MobiusHarmonicTree := .branch 41036525 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850176 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850240 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 23362851 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850304 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850368 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 25851216 d463 d464
private def d458 : MobiusHarmonicTree := .branch 49214067 d459 d462
private def d450 : MobiusHarmonicTree := .branch 90250592 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850432 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850496 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 25672201 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850560 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850624 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 24810088 d471 d472
private def d466 : MobiusHarmonicTree := .branch 50482289 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850688 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850752 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 24509003 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850816 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850880 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 23609766 d478 d479
private def d473 : MobiusHarmonicTree := .branch 48118769 d474 d477
private def d465 : MobiusHarmonicTree := .branch 98601058 d466 d473
private def d449 : MobiusHarmonicTree := .branch 188851650 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 850944 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851008 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 22997491 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851072 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851136 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 23371212 d487 d488
private def d482 : MobiusHarmonicTree := .branch 46368703 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851200 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851264 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 24174699 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851328 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851392 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 24814722 d494 d495
private def d489 : MobiusHarmonicTree := .branch 48989421 d490 d493
private def d481 : MobiusHarmonicTree := .branch 95358124 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851456 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851520 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 24621919 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851584 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851648 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 24665186 d502 d503
private def d497 : MobiusHarmonicTree := .branch 49287105 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851712 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851776 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 24856389 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851840 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock103 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 851904 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 25112068 d509 d510
private def d504 : MobiusHarmonicTree := .branch 49968457 d505 d508
private def d496 : MobiusHarmonicTree := .branch 99255562 d497 d504
private def d480 : MobiusHarmonicTree := .branch 194613686 d481 d496
private def d448 : MobiusHarmonicTree := .branch 383465336 d449 d480
private def d384 : MobiusHarmonicTree := .branch 728647643 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1740251426 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3352037715 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 835584 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 835584 3352037715 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 835584 1611786289 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 835584 779274014 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 835584 427523715 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 835584 217179111 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 835584 101836246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 835584 49459635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 835584 24114276 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 835712 25345359 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 835840 52376611 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 835840 26442136 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 835968 25934475 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 836096 115342865 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 836096 57568274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 836096 27798547 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 836224 29769727 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 836352 57774591 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 836352 29774752 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 836480 27999839 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 836608 210344604 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 836608 106125297 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 836608 53849849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 836608 26739360 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 836736 27110489 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 836864 52275448 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 836864 26298638 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 836992 25976810 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 837120 104219307 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 837120 53303452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 837120 27186460 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 837248 26116992 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 837376 50915855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 837376 26022256 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 837504 24893599 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 837632 351750299 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 837632 179285506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 837632 90648767 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 837632 46200796 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 837632 23368953 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 837760 22831843 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 837888 44447971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 837888 22084877 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 838016 22363094 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 838144 88636739 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 838144 43548231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 838144 22586359 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 838272 20961872 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 838400 45088508 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 838400 21627695 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 838528 23460813 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 838656 172464793 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 838656 89956710 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 838656 46381734 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 838656 23879335 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 838784 22502399 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 838912 43574976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 838912 21746808 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 839040 21828168 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 839168 82508083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 839168 41269224 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 839168 20485467 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 839296 20783757 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 839424 41238859 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 839424 20990233 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 839552 20248626 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 839680 832512275 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 839680 385402068 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 839680 189015259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 839680 91819917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 839680 44743608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 839680 21991257 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 839808 22752351 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 839936 47076309 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 839936 23503642 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 840064 23572667 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 840192 97195342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 840192 49752583 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 840192 24581851 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 840320 25170732 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 840448 47442759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 840448 24410207 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 840576 23032552 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 840704 196386809 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 840704 90330243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 840704 44839141 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 840704 22686482 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 840832 22152659 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 840960 45491102 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 840960 22118336 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 841088 23372766 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 841216 106056566 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 841216 54498547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 841216 26727159 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 841344 27771388 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 841472 51558019 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 841472 26229514 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 841600 25328505 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 841728 447110207 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 841728 207145527 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 841728 94842532 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 841728 46542526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 841728 23044970 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 841856 23497556 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 841984 48300006 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 841984 23527234 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 842112 24772772 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 842240 112302995 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 842240 54279121 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 842240 26244763 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 842368 28034358 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 842496 58023874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 842496 30014584 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 842624 28009290 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 842752 239964680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 842752 111589264 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 842752 53918894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 842752 27164966 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 842880 26753928 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 843008 57670370 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 843008 27806710 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 843136 29863660 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 843264 128375416 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 843264 63992936 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 843264 32097878 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 843392 31895058 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 843520 64382480 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 843520 32162864 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 843648 32219616 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 843776 1740251426 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 843776 1011603783 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 843776 582780337 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 843776 283491454 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 843776 135596540 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 843776 66553949 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 843776 33236226 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 843904 33317723 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 844032 69042591 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 844032 33664464 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 844160 35378127 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 844288 147894914 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 844288 72716579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 844288 35640425 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 844416 37076154 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 844544 75178335 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 844544 36914238 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 844672 38264097 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 844800 299288883 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 844800 153256932 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 844800 78115658 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 844800 38771993 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 844928 39343665 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 845056 75141274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 845056 37742704 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 845184 37398570 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 845312 146031951 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 845312 74732948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 845312 37903941 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 845440 36829007 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 845568 71299003 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 845568 36466289 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 845696 34832714 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 845824 428823446 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 845824 233500788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 845824 127840297 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 845824 66708371 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 845824 32843651 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 845952 33864720 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 846080 61131926 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 846080 31681487 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 846208 29450439 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 846336 105660491 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 846336 56159821 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 846336 28982828 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 846464 27176993 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 846592 49500670 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 846592 25332680 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 846720 24167990 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 846848 195322658 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 846848 98160162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 846848 47816071 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 846848 23435811 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 846976 24380260 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 847104 50344091 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 847104 25114338 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 847232 25229753 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 847360 97162496 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 847360 48554345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 847360 24985228 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 847488 23569117 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 847616 48608151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 847616 25221863 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 847744 23386288 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 847872 728647643 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 847872 345182307 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 847872 183369595 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 847872 93662417 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 847872 48039137 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 847872 24394575 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 848000 23644562 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 848128 45623280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 848128 23260149 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 848256 22363131 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 848384 89707178 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 848384 44298816 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 848384 21913011 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 848512 22385805 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 848640 45408362 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 848640 22847858 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 848768 22560504 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 848896 161812712 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 848896 86935638 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 848896 44355769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 848896 22130683 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 849024 22225086 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 849152 42579869 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 849152 21915601 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 849280 20664268 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 849408 74877074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 849408 37630200 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 849408 19262651 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 849536 18367549 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 849664 37246874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 849664 18511874 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 849792 18735000 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 849920 383465336 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 849920 188851650 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 849920 90250592 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 849920 41036525 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 849920 19682781 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 850048 21353744 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 850176 49214067 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 850176 23362851 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 850304 25851216 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 850432 98601058 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 850432 50482289 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 850432 25672201 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 850560 24810088 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 850688 48118769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 850688 24509003 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 850816 23609766 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 850944 194613686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 850944 95358124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 850944 46368703 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 850944 22997491 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 851072 23371212 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 851200 48989421 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 851200 24174699 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 851328 24814722 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 851456 99255562 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 851456 49287105 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 851456 24621919 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 851584 24665186 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 851712 49968457 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 851712 24856389 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 851840 25112068 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 835584 (MobiusHarmonicTree.branch 3352037715 mobiusHarmonicBlock102 mobiusHarmonicBlock103) = true := Helfgott.combined

#print axioms solution
