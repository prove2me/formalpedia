-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair000_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T21:44:24.434401+00:00
-- url     : https://prove2.me/submissions/4882aec8-6408-47b6-ac63-49cb875f6962

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 0 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 8237791951 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 128 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 192 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 1633701923 d11 d12
private def d6 : MobiusHarmonicTree := .branch 9871493874 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 1123529267 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 448 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 1067683604 d18 d19
private def d13 : MobiusHarmonicTree := .branch 2191212871 d14 d17
private def d5 : MobiusHarmonicTree := .branch 12062706745 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 512 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 576 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 732160949 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 640 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 704 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 1052129944 d26 d27
private def d21 : MobiusHarmonicTree := .branch 1784290893 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 768 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 218931477 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 896 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 960 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 268444446 d33 d34
private def d28 : MobiusHarmonicTree := .branch 487375923 d29 d32
private def d20 : MobiusHarmonicTree := .branch 2271666816 d21 d28
private def d4 : MobiusHarmonicTree := .branch 14334373561 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1024 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1088 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 993430153 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1152 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1216 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 335571972 d42 d43
private def d37 : MobiusHarmonicTree := .branch 1329002125 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1280 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1344 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 368371878 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1408 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1472 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 376235879 d49 d50
private def d44 : MobiusHarmonicTree := .branch 744607757 d45 d48
private def d36 : MobiusHarmonicTree := .branch 2073609882 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1536 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1600 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 589787051 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1664 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1728 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 731186225 d57 d58
private def d52 : MobiusHarmonicTree := .branch 1320973276 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1792 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1856 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 256894625 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1920 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1984 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 221888536 d64 d65
private def d59 : MobiusHarmonicTree := .branch 478783161 d60 d63
private def d51 : MobiusHarmonicTree := .branch 1799756437 d52 d59
private def d35 : MobiusHarmonicTree := .branch 3873366319 d36 d51
private def d3 : MobiusHarmonicTree := .branch 18207739880 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2048 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2112 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 190470443 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2176 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2240 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 377718572 d74 d75
private def d69 : MobiusHarmonicTree := .branch 568189015 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2304 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2368 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 324542972 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2432 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2496 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 278712801 d81 d82
private def d76 : MobiusHarmonicTree := .branch 603255773 d77 d80
private def d68 : MobiusHarmonicTree := .branch 1171444788 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2560 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2624 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 312131189 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2688 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2752 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 652349893 d89 d90
private def d84 : MobiusHarmonicTree := .branch 964481082 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2816 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2880 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 865198542 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 2944 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3008 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 368075017 d96 d97
private def d91 : MobiusHarmonicTree := .branch 1233273559 d92 d95
private def d83 : MobiusHarmonicTree := .branch 2197754641 d84 d91
private def d67 : MobiusHarmonicTree := .branch 3369199429 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3072 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3136 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 242870356 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3200 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3264 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 650241842 d105 d106
private def d100 : MobiusHarmonicTree := .branch 893112198 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3328 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3392 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 576824458 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3456 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3520 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 315854934 d112 d113
private def d107 : MobiusHarmonicTree := .branch 892679392 d108 d111
private def d99 : MobiusHarmonicTree := .branch 1785791590 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3584 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3648 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 163796963 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3712 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3776 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 246198511 d120 d121
private def d115 : MobiusHarmonicTree := .branch 409995474 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3840 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3904 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 361397397 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 3968 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4032 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 406544915 d127 d128
private def d122 : MobiusHarmonicTree := .branch 767942312 d123 d126
private def d114 : MobiusHarmonicTree := .branch 1177937786 d115 d122
private def d98 : MobiusHarmonicTree := .branch 2963729376 d99 d114
private def d66 : MobiusHarmonicTree := .branch 6332928805 d67 d98
private def d2 : MobiusHarmonicTree := .branch 24540668685 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4096 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4160 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 415121832 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4224 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4288 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 341669011 d138 d139
private def d133 : MobiusHarmonicTree := .branch 756790843 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4352 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4416 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 244585458 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4480 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4544 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 105273136 d145 d146
private def d140 : MobiusHarmonicTree := .branch 349858594 d141 d144
private def d132 : MobiusHarmonicTree := .branch 1106649437 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4608 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4672 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 71055770 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4736 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4800 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 239441181 d153 d154
private def d148 : MobiusHarmonicTree := .branch 310496951 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4864 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4928 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 372738263 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 4992 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5056 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 72433493 d160 d161
private def d155 : MobiusHarmonicTree := .branch 445171756 d156 d159
private def d147 : MobiusHarmonicTree := .branch 755668707 d148 d155
private def d131 : MobiusHarmonicTree := .branch 1862318144 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5120 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5184 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 39788967 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5248 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5312 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 68986817 d169 d170
private def d164 : MobiusHarmonicTree := .branch 108775784 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5376 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5440 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 225885348 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5504 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5568 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 189755624 d176 d177
private def d171 : MobiusHarmonicTree := .branch 415640972 d172 d175
private def d163 : MobiusHarmonicTree := .branch 524416756 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5632 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5696 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 194214420 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5760 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5824 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 107138143 d184 d185
private def d179 : MobiusHarmonicTree := .branch 301352563 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5888 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 5952 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 98309555 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6016 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6080 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 51640054 d191 d192
private def d186 : MobiusHarmonicTree := .branch 149949609 d187 d190
private def d178 : MobiusHarmonicTree := .branch 451302172 d179 d186
private def d162 : MobiusHarmonicTree := .branch 975718928 d163 d178
private def d130 : MobiusHarmonicTree := .branch 2838037072 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6144 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6208 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 129507820 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6272 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6336 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 377112714 d201 d202
private def d196 : MobiusHarmonicTree := .branch 506620534 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6400 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6464 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 323923833 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6528 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6592 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 317794423 d208 d209
private def d203 : MobiusHarmonicTree := .branch 641718256 d204 d207
private def d195 : MobiusHarmonicTree := .branch 1148338790 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6656 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6720 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 296079504 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6784 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6848 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 313295525 d216 d217
private def d211 : MobiusHarmonicTree := .branch 609375029 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6912 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 6976 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 402914725 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7040 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7104 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 274407747 d223 d224
private def d218 : MobiusHarmonicTree := .branch 677322472 d219 d222
private def d210 : MobiusHarmonicTree := .branch 1286697501 d211 d218
private def d194 : MobiusHarmonicTree := .branch 2435036291 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7168 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7232 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 53740954 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7296 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7360 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 138170141 d232 d233
private def d227 : MobiusHarmonicTree := .branch 191911095 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7424 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7488 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 256314078 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7552 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7616 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 50725193 d239 d240
private def d234 : MobiusHarmonicTree := .branch 307039271 d235 d238
private def d226 : MobiusHarmonicTree := .branch 498950366 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7680 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7744 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 65258765 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7808 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7872 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 27309212 d247 d248
private def d242 : MobiusHarmonicTree := .branch 92567977 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 7936 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8000 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 92060936 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8064 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock000 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8128 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 245510678 d254 d255
private def d249 : MobiusHarmonicTree := .branch 337571614 d250 d253
private def d241 : MobiusHarmonicTree := .branch 430139591 d242 d249
private def d225 : MobiusHarmonicTree := .branch 929089957 d226 d241
private def d193 : MobiusHarmonicTree := .branch 3364126248 d194 d225
private def d129 : MobiusHarmonicTree := .branch 6202163320 d130 d193
private def d1 : MobiusHarmonicTree := .branch 30742832005 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8192 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8256 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 274276150 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8320 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8384 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 313507635 d266 d267
private def d261 : MobiusHarmonicTree := .branch 587783785 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8448 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8512 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 423937105 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8576 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8640 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 377700944 d273 d274
private def d268 : MobiusHarmonicTree := .branch 801638049 d269 d272
private def d260 : MobiusHarmonicTree := .branch 1389421834 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8704 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8768 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 196361757 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8832 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8896 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 83642713 d281 d282
private def d276 : MobiusHarmonicTree := .branch 280004470 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 8960 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9024 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 30054943 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9088 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9152 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 38510062 d288 d289
private def d283 : MobiusHarmonicTree := .branch 68565005 d284 d287
private def d275 : MobiusHarmonicTree := .branch 348569475 d276 d283
private def d259 : MobiusHarmonicTree := .branch 1737991309 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9216 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9280 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 43585425 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9344 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9408 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 124953173 d297 d298
private def d292 : MobiusHarmonicTree := .branch 168538598 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9472 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9536 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 280880305 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9600 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9664 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 273502390 d304 d305
private def d299 : MobiusHarmonicTree := .branch 554382695 d300 d303
private def d291 : MobiusHarmonicTree := .branch 722921293 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9728 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9792 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 453130585 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9856 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9920 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 482402330 d312 d313
private def d307 : MobiusHarmonicTree := .branch 935532915 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 9984 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10048 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 243412763 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10112 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10176 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 230961092 d319 d320
private def d314 : MobiusHarmonicTree := .branch 474373855 d315 d318
private def d306 : MobiusHarmonicTree := .branch 1409906770 d307 d314
private def d290 : MobiusHarmonicTree := .branch 2132828063 d291 d306
private def d258 : MobiusHarmonicTree := .branch 3870819372 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10240 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10304 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 352605510 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10368 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10432 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 310658093 d329 d330
private def d324 : MobiusHarmonicTree := .branch 663263603 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10496 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10560 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 255080872 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10624 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10688 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 237042377 d336 d337
private def d331 : MobiusHarmonicTree := .branch 492123249 d332 d335
private def d323 : MobiusHarmonicTree := .branch 1155386852 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10752 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10816 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 170117673 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10880 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 10944 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 103346994 d344 d345
private def d339 : MobiusHarmonicTree := .branch 273464667 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11008 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11072 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 27757048 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11136 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11200 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 27962035 d351 d352
private def d346 : MobiusHarmonicTree := .branch 55719083 d347 d350
private def d338 : MobiusHarmonicTree := .branch 329183750 d339 d346
private def d322 : MobiusHarmonicTree := .branch 1484570602 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11264 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11328 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 42747856 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11392 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11456 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 129902112 d360 d361
private def d355 : MobiusHarmonicTree := .branch 172649968 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11520 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11584 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 141426348 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11648 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11712 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 290121988 d367 d368
private def d362 : MobiusHarmonicTree := .branch 431548336 d363 d366
private def d354 : MobiusHarmonicTree := .branch 604198304 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11776 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11840 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 351873351 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11904 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 11968 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 216742779 d375 d376
private def d370 : MobiusHarmonicTree := .branch 568616130 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12032 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12096 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 182158133 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12160 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12224 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 194759415 d382 d383
private def d377 : MobiusHarmonicTree := .branch 376917548 d378 d381
private def d369 : MobiusHarmonicTree := .branch 945533678 d370 d377
private def d353 : MobiusHarmonicTree := .branch 1549731982 d354 d369
private def d321 : MobiusHarmonicTree := .branch 3034302584 d322 d353
private def d257 : MobiusHarmonicTree := .branch 6905121956 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12288 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12352 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 176992836 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12416 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12480 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 124276771 d393 d394
private def d388 : MobiusHarmonicTree := .branch 301269607 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12544 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12608 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 25851984 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12672 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12736 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 80846107 d400 d401
private def d395 : MobiusHarmonicTree := .branch 106698091 d396 d399
private def d387 : MobiusHarmonicTree := .branch 407967698 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12800 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12864 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 53861710 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12928 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 12992 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 82495111 d408 d409
private def d403 : MobiusHarmonicTree := .branch 136356821 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13056 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13120 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 98510253 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13184 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13248 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 131049058 d415 d416
private def d410 : MobiusHarmonicTree := .branch 229559311 d411 d414
private def d402 : MobiusHarmonicTree := .branch 365916132 d403 d410
private def d386 : MobiusHarmonicTree := .branch 773883830 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13312 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13376 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 81154453 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13440 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13504 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 18200281 d424 d425
private def d419 : MobiusHarmonicTree := .branch 99354734 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13568 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13632 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 55103356 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13696 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13760 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 21600760 d431 d432
private def d426 : MobiusHarmonicTree := .branch 76704116 d427 d430
private def d418 : MobiusHarmonicTree := .branch 176058850 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13824 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13888 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 28076007 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 13952 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14016 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 118173897 d439 d440
private def d434 : MobiusHarmonicTree := .branch 146249904 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14080 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14144 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 145547567 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14208 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14272 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 172397926 d446 d447
private def d441 : MobiusHarmonicTree := .branch 317945493 d442 d445
private def d433 : MobiusHarmonicTree := .branch 464195397 d434 d441
private def d417 : MobiusHarmonicTree := .branch 640254247 d418 d433
private def d385 : MobiusHarmonicTree := .branch 1414138077 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14336 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14400 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 126411982 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14464 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14528 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 99786055 d456 d457
private def d451 : MobiusHarmonicTree := .branch 226198037 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14592 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14656 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 30372464 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14720 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14784 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 63503563 d463 d464
private def d458 : MobiusHarmonicTree := .branch 93876027 d459 d462
private def d450 : MobiusHarmonicTree := .branch 320074064 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14848 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14912 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 145489873 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 14976 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15040 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 41374622 d471 d472
private def d466 : MobiusHarmonicTree := .branch 186864495 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15104 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15168 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 58271130 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15232 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15296 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 50623156 d478 d479
private def d473 : MobiusHarmonicTree := .branch 108894286 d474 d477
private def d465 : MobiusHarmonicTree := .branch 295758781 d466 d473
private def d449 : MobiusHarmonicTree := .branch 615832845 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15360 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15424 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 68657671 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15488 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15552 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 116209121 d487 d488
private def d482 : MobiusHarmonicTree := .branch 184866792 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15616 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15680 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 177362749 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15744 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15808 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 219941433 d494 d495
private def d489 : MobiusHarmonicTree := .branch 397304182 d490 d493
private def d481 : MobiusHarmonicTree := .branch 582170974 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15872 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 15936 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 179829233 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16000 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16064 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 229414631 d502 d503
private def d497 : MobiusHarmonicTree := .branch 409243864 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16128 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16192 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 292098650 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16256 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock001 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16320 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 261264237 d509 d510
private def d504 : MobiusHarmonicTree := .branch 553362887 d505 d508
private def d496 : MobiusHarmonicTree := .branch 962606751 d497 d504
private def d480 : MobiusHarmonicTree := .branch 1544777725 d481 d496
private def d448 : MobiusHarmonicTree := .branch 2160610570 d449 d480
private def d384 : MobiusHarmonicTree := .branch 3574748647 d385 d448
private def d256 : MobiusHarmonicTree := .branch 10479870603 d257 d384
private def d0 : MobiusHarmonicTree := .branch 41222702608 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 0 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 0 41222702608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 0 30742832005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 0 24540668685 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 0 18207739880 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 0 14334373561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 0 12062706745 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 0 9871493874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 0 8237791951 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 128 1633701923 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 256 2191212871 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 256 1123529267 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 384 1067683604 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 512 2271666816 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 512 1784290893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 512 732160949 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 640 1052129944 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 768 487375923 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 768 218931477 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 896 268444446 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1024 3873366319 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1024 2073609882 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1024 1329002125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1024 993430153 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1152 335571972 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1280 744607757 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1280 368371878 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1408 376235879 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1536 1799756437 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1536 1320973276 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1536 589787051 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1664 731186225 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1792 478783161 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1792 256894625 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1920 221888536 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 2048 6332928805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 2048 3369199429 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 2048 1171444788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 2048 568189015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 2048 190470443 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 2176 377718572 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 2304 603255773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 2304 324542972 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 2432 278712801 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 2560 2197754641 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 2560 964481082 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 2560 312131189 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 2688 652349893 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 2816 1233273559 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 2816 865198542 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 2944 368075017 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 3072 2963729376 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 3072 1785791590 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 3072 893112198 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 3072 242870356 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 3200 650241842 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 3328 892679392 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 3328 576824458 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 3456 315854934 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 3584 1177937786 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 3584 409995474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 3584 163796963 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 3712 246198511 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 3840 767942312 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 3840 361397397 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 3968 406544915 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 4096 6202163320 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 4096 2838037072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 4096 1862318144 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 4096 1106649437 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 4096 756790843 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 4096 415121832 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 4224 341669011 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 4352 349858594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 4352 244585458 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 4480 105273136 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 4608 755668707 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 4608 310496951 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 4608 71055770 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 4736 239441181 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 4864 445171756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 4864 372738263 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 4992 72433493 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 5120 975718928 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 5120 524416756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 5120 108775784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 5120 39788967 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 5248 68986817 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 5376 415640972 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 5376 225885348 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 5504 189755624 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 5632 451302172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 5632 301352563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 5632 194214420 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 5760 107138143 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 5888 149949609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 5888 98309555 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 6016 51640054 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 6144 3364126248 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 6144 2435036291 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 6144 1148338790 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 6144 506620534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 6144 129507820 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 6272 377112714 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 6400 641718256 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 6400 323923833 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 6528 317794423 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 6656 1286697501 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 6656 609375029 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 6656 296079504 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 6784 313295525 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 6912 677322472 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 6912 402914725 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 7040 274407747 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 7168 929089957 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 7168 498950366 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 7168 191911095 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 7168 53740954 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 7296 138170141 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 7424 307039271 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 7424 256314078 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 7552 50725193 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 7680 430139591 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 7680 92567977 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 7680 65258765 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 7808 27309212 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 7936 337571614 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 7936 92060936 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 8064 245510678 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 8192 10479870603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 8192 6905121956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 8192 3870819372 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 8192 1737991309 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 8192 1389421834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 8192 587783785 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 8192 274276150 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 8320 313507635 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 8448 801638049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 8448 423937105 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 8576 377700944 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 8704 348569475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 8704 280004470 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 8704 196361757 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 8832 83642713 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 8960 68565005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 8960 30054943 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 9088 38510062 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 9216 2132828063 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 9216 722921293 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 9216 168538598 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 9216 43585425 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 9344 124953173 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 9472 554382695 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 9472 280880305 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 9600 273502390 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 9728 1409906770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 9728 935532915 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 9728 453130585 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 9856 482402330 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 9984 474373855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 9984 243412763 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 10112 230961092 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 10240 3034302584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 10240 1484570602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 10240 1155386852 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 10240 663263603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 10240 352605510 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 10368 310658093 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 10496 492123249 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 10496 255080872 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 10624 237042377 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 10752 329183750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 10752 273464667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 10752 170117673 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 10880 103346994 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 11008 55719083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 11008 27757048 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 11136 27962035 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 11264 1549731982 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 11264 604198304 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 11264 172649968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 11264 42747856 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 11392 129902112 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 11520 431548336 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 11520 141426348 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 11648 290121988 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 11776 945533678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 11776 568616130 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 11776 351873351 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 11904 216742779 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 12032 376917548 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 12032 182158133 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 12160 194759415 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 12288 3574748647 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 12288 1414138077 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 12288 773883830 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 12288 407967698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 12288 301269607 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 12288 176992836 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 12416 124276771 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 12544 106698091 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 12544 25851984 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 12672 80846107 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 12800 365916132 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 12800 136356821 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 12800 53861710 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 12928 82495111 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 13056 229559311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 13056 98510253 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 13184 131049058 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 13312 640254247 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 13312 176058850 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 13312 99354734 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 13312 81154453 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 13440 18200281 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 13568 76704116 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 13568 55103356 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 13696 21600760 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 13824 464195397 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 13824 146249904 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 13824 28076007 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 13952 118173897 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 14080 317945493 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 14080 145547567 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 14208 172397926 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 14336 2160610570 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 14336 615832845 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 14336 320074064 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 14336 226198037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 14336 126411982 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 14464 99786055 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 14592 93876027 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 14592 30372464 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 14720 63503563 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 14848 295758781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 14848 186864495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 14848 145489873 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 14976 41374622 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 15104 108894286 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 15104 58271130 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 15232 50623156 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 15360 1544777725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 15360 582170974 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 15360 184866792 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 15360 68657671 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 15488 116209121 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 15616 397304182 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 15616 177362749 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 15744 219941433 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 15872 962606751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 15872 409243864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 15872 179829233 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 16000 229414631 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 16128 553362887 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 16128 292098650 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 16256 261264237 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 0 (MobiusHarmonicTree.branch 41222702608 mobiusHarmonicBlock000 mobiusHarmonicBlock001) = true := Helfgott.combined

#print axioms solution
