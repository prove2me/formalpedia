-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair023_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:18:38.291066+00:00
-- url     : https://prove2.me/submissions/128358c7-a3db-4348-8539-fb059a321350

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376832 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376896 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 1806887 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 376960 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377024 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 1403234 d11 d12
private def d6 : MobiusHarmonicTree := .branch 3210121 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377088 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377152 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 1187884 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377216 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377280 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 556671 d18 d19
private def d13 : MobiusHarmonicTree := .branch 1744555 d14 d17
private def d5 : MobiusHarmonicTree := .branch 4954676 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377344 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377408 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 2986085 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377472 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377536 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 2561550 d26 d27
private def d21 : MobiusHarmonicTree := .branch 5547635 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377600 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377664 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 1636380 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377728 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377792 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 3300808 d33 d34
private def d28 : MobiusHarmonicTree := .branch 4937188 d29 d32
private def d20 : MobiusHarmonicTree := .branch 10484823 d21 d28
private def d4 : MobiusHarmonicTree := .branch 15439499 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377856 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377920 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 5977522 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 377984 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378048 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 6790177 d42 d43
private def d37 : MobiusHarmonicTree := .branch 12767699 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378112 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378176 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 3384925 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378240 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378304 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 1287286 d49 d50
private def d44 : MobiusHarmonicTree := .branch 4672211 d45 d48
private def d36 : MobiusHarmonicTree := .branch 17439910 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378368 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378432 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 5155434 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378496 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378560 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 4424844 d57 d58
private def d52 : MobiusHarmonicTree := .branch 9580278 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378624 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378688 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 3789435 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378752 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378816 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 3986105 d64 d65
private def d59 : MobiusHarmonicTree := .branch 7775540 d60 d63
private def d51 : MobiusHarmonicTree := .branch 17355818 d52 d59
private def d35 : MobiusHarmonicTree := .branch 34795728 d36 d51
private def d3 : MobiusHarmonicTree := .branch 50235227 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378880 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 378944 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 4557495 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379008 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379072 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 5497713 d74 d75
private def d69 : MobiusHarmonicTree := .branch 10055208 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379136 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379200 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 5018494 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379264 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379328 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 5757572 d81 d82
private def d76 : MobiusHarmonicTree := .branch 10776066 d77 d80
private def d68 : MobiusHarmonicTree := .branch 20831274 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379392 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379456 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 9690177 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379520 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379584 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 10271961 d89 d90
private def d84 : MobiusHarmonicTree := .branch 19962138 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379648 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379712 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 7971895 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379776 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379840 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 8092979 d96 d97
private def d91 : MobiusHarmonicTree := .branch 16064874 d92 d95
private def d83 : MobiusHarmonicTree := .branch 36027012 d84 d91
private def d67 : MobiusHarmonicTree := .branch 56858286 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379904 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 379968 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 9161322 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380032 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380096 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 9055720 d105 d106
private def d100 : MobiusHarmonicTree := .branch 18217042 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380160 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380224 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 10070387 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380288 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380352 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 8621241 d112 d113
private def d107 : MobiusHarmonicTree := .branch 18691628 d108 d111
private def d99 : MobiusHarmonicTree := .branch 36908670 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380416 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380480 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 6657438 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380544 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380608 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 9676655 d120 d121
private def d115 : MobiusHarmonicTree := .branch 16334093 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380672 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380736 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 11858646 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380800 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380864 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 12070133 d127 d128
private def d122 : MobiusHarmonicTree := .branch 23928779 d123 d126
private def d114 : MobiusHarmonicTree := .branch 40262872 d115 d122
private def d98 : MobiusHarmonicTree := .branch 77171542 d99 d114
private def d66 : MobiusHarmonicTree := .branch 134029828 d67 d98
private def d2 : MobiusHarmonicTree := .branch 184265055 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380928 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 380992 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 8013568 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381056 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381120 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 7118442 d138 d139
private def d133 : MobiusHarmonicTree := .branch 15132010 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381184 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381248 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 8015898 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381312 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381376 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 6350846 d145 d146
private def d140 : MobiusHarmonicTree := .branch 14366744 d141 d144
private def d132 : MobiusHarmonicTree := .branch 29498754 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381440 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381504 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 6713068 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381568 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381632 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 5154213 d153 d154
private def d148 : MobiusHarmonicTree := .branch 11867281 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381696 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381760 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 6962503 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381824 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381888 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 6931425 d160 d161
private def d155 : MobiusHarmonicTree := .branch 13893928 d156 d159
private def d147 : MobiusHarmonicTree := .branch 25761209 d148 d155
private def d131 : MobiusHarmonicTree := .branch 55259963 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 381952 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382016 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 4725065 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382080 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382144 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 7091492 d169 d170
private def d164 : MobiusHarmonicTree := .branch 11816557 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382208 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382272 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 11863449 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382336 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382400 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 9851068 d176 d177
private def d171 : MobiusHarmonicTree := .branch 21714517 d172 d175
private def d163 : MobiusHarmonicTree := .branch 33531074 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382464 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382528 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 12080236 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382592 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382656 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 9212120 d184 d185
private def d179 : MobiusHarmonicTree := .branch 21292356 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382720 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382784 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 5400080 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382848 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382912 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 2339905 d191 d192
private def d186 : MobiusHarmonicTree := .branch 7739985 d187 d190
private def d178 : MobiusHarmonicTree := .branch 29032341 d179 d186
private def d162 : MobiusHarmonicTree := .branch 62563415 d163 d178
private def d130 : MobiusHarmonicTree := .branch 117823378 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 382976 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383040 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 4845501 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383104 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383168 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 2257638 d201 d202
private def d196 : MobiusHarmonicTree := .branch 7103139 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383232 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383296 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 2371644 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383360 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383424 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 2589900 d208 d209
private def d203 : MobiusHarmonicTree := .branch 4961544 d204 d207
private def d195 : MobiusHarmonicTree := .branch 12064683 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383488 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383552 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 2448168 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383616 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383680 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 2017374 d216 d217
private def d211 : MobiusHarmonicTree := .branch 4465542 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383744 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383808 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 607164 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383872 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 383936 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 922075 d223 d224
private def d218 : MobiusHarmonicTree := .branch 1529239 d219 d222
private def d210 : MobiusHarmonicTree := .branch 5994781 d211 d218
private def d194 : MobiusHarmonicTree := .branch 18059464 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384000 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384064 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 3528115 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384128 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384192 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 1540939 d232 d233
private def d227 : MobiusHarmonicTree := .branch 5069054 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384256 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384320 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 4033208 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384384 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384448 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 2070647 d239 d240
private def d234 : MobiusHarmonicTree := .branch 6103855 d235 d238
private def d226 : MobiusHarmonicTree := .branch 11172909 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384512 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384576 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 2488518 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384640 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384704 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 1310171 d247 d248
private def d242 : MobiusHarmonicTree := .branch 3798689 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384768 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384832 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 1255122 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384896 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock046 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 384960 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 1039155 d254 d255
private def d249 : MobiusHarmonicTree := .branch 2294277 d250 d253
private def d241 : MobiusHarmonicTree := .branch 6092966 d242 d249
private def d225 : MobiusHarmonicTree := .branch 17265875 d226 d241
private def d193 : MobiusHarmonicTree := .branch 35325339 d194 d225
private def d129 : MobiusHarmonicTree := .branch 153148717 d130 d193
private def d1 : MobiusHarmonicTree := .branch 337413772 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385024 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385088 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 724572 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385152 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385216 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 2588135 d266 d267
private def d261 : MobiusHarmonicTree := .branch 3312707 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385280 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385344 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 3531933 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385408 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385472 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 1969036 d273 d274
private def d268 : MobiusHarmonicTree := .branch 5500969 d269 d272
private def d260 : MobiusHarmonicTree := .branch 8813676 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385536 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385600 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 1750613 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385664 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385728 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 2185417 d281 d282
private def d276 : MobiusHarmonicTree := .branch 3936030 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385792 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385856 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 5090041 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385920 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 385984 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 3665934 d288 d289
private def d283 : MobiusHarmonicTree := .branch 8755975 d284 d287
private def d275 : MobiusHarmonicTree := .branch 12692005 d276 d283
private def d259 : MobiusHarmonicTree := .branch 21505681 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386048 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386112 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 4247644 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386176 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386240 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 3640265 d297 d298
private def d292 : MobiusHarmonicTree := .branch 7887909 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386304 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386368 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 2761759 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386432 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386496 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 1379111 d304 d305
private def d299 : MobiusHarmonicTree := .branch 4140870 d300 d303
private def d291 : MobiusHarmonicTree := .branch 12028779 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386560 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386624 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 1528695 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386688 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386752 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 1372945 d312 d313
private def d307 : MobiusHarmonicTree := .branch 2901640 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386816 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386880 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 7891262 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 386944 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387008 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 10113561 d319 d320
private def d314 : MobiusHarmonicTree := .branch 18004823 d315 d318
private def d306 : MobiusHarmonicTree := .branch 20906463 d307 d314
private def d290 : MobiusHarmonicTree := .branch 32935242 d291 d306
private def d258 : MobiusHarmonicTree := .branch 54440923 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387072 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387136 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 10319405 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387200 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387264 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 13148761 d329 d330
private def d324 : MobiusHarmonicTree := .branch 23468166 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387328 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387392 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 14365311 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387456 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387520 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 15914066 d336 d337
private def d331 : MobiusHarmonicTree := .branch 30279377 d332 d335
private def d323 : MobiusHarmonicTree := .branch 53747543 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387584 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387648 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 19123109 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387712 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387776 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 17804229 d344 d345
private def d339 : MobiusHarmonicTree := .branch 36927338 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387840 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387904 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 20432891 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 387968 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388032 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 17916071 d351 d352
private def d346 : MobiusHarmonicTree := .branch 38348962 d347 d350
private def d338 : MobiusHarmonicTree := .branch 75276300 d339 d346
private def d322 : MobiusHarmonicTree := .branch 129023843 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388096 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388160 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 18585260 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388224 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388288 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 18308673 d360 d361
private def d355 : MobiusHarmonicTree := .branch 36893933 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388352 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388416 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 19224212 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388480 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388544 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 22764414 d367 d368
private def d362 : MobiusHarmonicTree := .branch 41988626 d363 d366
private def d354 : MobiusHarmonicTree := .branch 78882559 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388608 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388672 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 24964721 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388736 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388800 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 24933201 d375 d376
private def d370 : MobiusHarmonicTree := .branch 49897922 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388864 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388928 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 22935049 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 388992 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389056 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 20251739 d382 d383
private def d377 : MobiusHarmonicTree := .branch 43186788 d378 d381
private def d369 : MobiusHarmonicTree := .branch 93084710 d370 d377
private def d353 : MobiusHarmonicTree := .branch 171967269 d354 d369
private def d321 : MobiusHarmonicTree := .branch 300991112 d322 d353
private def d257 : MobiusHarmonicTree := .branch 355432035 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389120 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389184 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 16699211 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389248 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389312 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 15126736 d393 d394
private def d388 : MobiusHarmonicTree := .branch 31825947 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389376 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389440 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 18685751 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389504 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389568 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 19075217 d400 d401
private def d395 : MobiusHarmonicTree := .branch 37760968 d396 d399
private def d387 : MobiusHarmonicTree := .branch 69586915 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389632 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389696 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 20798314 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389760 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389824 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 20747884 d408 d409
private def d403 : MobiusHarmonicTree := .branch 41546198 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389888 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 389952 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 20510373 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390016 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390080 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 20262585 d415 d416
private def d410 : MobiusHarmonicTree := .branch 40772958 d411 d414
private def d402 : MobiusHarmonicTree := .branch 82319156 d403 d410
private def d386 : MobiusHarmonicTree := .branch 151906071 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390144 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390208 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 19356503 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390272 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390336 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 20167312 d424 d425
private def d419 : MobiusHarmonicTree := .branch 39523815 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390400 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390464 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 15761022 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390528 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390592 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 13528209 d431 d432
private def d426 : MobiusHarmonicTree := .branch 29289231 d427 d430
private def d418 : MobiusHarmonicTree := .branch 68813046 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390656 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390720 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 12891709 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390784 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390848 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 11848664 d439 d440
private def d434 : MobiusHarmonicTree := .branch 24740373 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390912 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 390976 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 11875528 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391040 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391104 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 9851668 d446 d447
private def d441 : MobiusHarmonicTree := .branch 21727196 d442 d445
private def d433 : MobiusHarmonicTree := .branch 46467569 d434 d441
private def d417 : MobiusHarmonicTree := .branch 115280615 d418 d433
private def d385 : MobiusHarmonicTree := .branch 267186686 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391168 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391232 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 9447129 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391296 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391360 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 10752388 d456 d457
private def d451 : MobiusHarmonicTree := .branch 20199517 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391424 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391488 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 15085918 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391552 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391616 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 18656099 d463 d464
private def d458 : MobiusHarmonicTree := .branch 33742017 d459 d462
private def d450 : MobiusHarmonicTree := .branch 53941534 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391680 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391744 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 17332930 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391808 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391872 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 15068774 d471 d472
private def d466 : MobiusHarmonicTree := .branch 32401704 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 391936 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392000 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 16354607 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392064 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392128 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 17838714 d478 d479
private def d473 : MobiusHarmonicTree := .branch 34193321 d474 d477
private def d465 : MobiusHarmonicTree := .branch 66595025 d466 d473
private def d449 : MobiusHarmonicTree := .branch 120536559 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392192 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392256 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 12436107 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392320 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392384 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 6738448 d487 d488
private def d482 : MobiusHarmonicTree := .branch 19174555 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392448 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392512 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 4550288 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392576 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392640 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 4508037 d494 d495
private def d489 : MobiusHarmonicTree := .branch 9058325 d490 d493
private def d481 : MobiusHarmonicTree := .branch 28232880 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392704 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392768 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 2444353 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392832 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392896 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 1160659 d502 d503
private def d497 : MobiusHarmonicTree := .branch 3605012 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 392960 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393024 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 1053431 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393088 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock047 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 393152 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 1856820 d509 d510
private def d504 : MobiusHarmonicTree := .branch 2910251 d505 d508
private def d496 : MobiusHarmonicTree := .branch 6515263 d497 d504
private def d480 : MobiusHarmonicTree := .branch 34748143 d481 d496
private def d448 : MobiusHarmonicTree := .branch 155284702 d449 d480
private def d384 : MobiusHarmonicTree := .branch 422471388 d385 d448
private def d256 : MobiusHarmonicTree := .branch 777903423 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1115317195 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 376832 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 376832 1115317195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 376832 337413772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 376832 184265055 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 376832 50235227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 376832 15439499 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 376832 4954676 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 376832 3210121 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 376832 1806887 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 376960 1403234 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 377088 1744555 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 377088 1187884 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 377216 556671 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 377344 10484823 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 377344 5547635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 377344 2986085 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 377472 2561550 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 377600 4937188 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 377600 1636380 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 377728 3300808 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 377856 34795728 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 377856 17439910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 377856 12767699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 377856 5977522 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 377984 6790177 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 378112 4672211 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 378112 3384925 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 378240 1287286 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 378368 17355818 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 378368 9580278 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 378368 5155434 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 378496 4424844 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 378624 7775540 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 378624 3789435 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 378752 3986105 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 378880 134029828 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 378880 56858286 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 378880 20831274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 378880 10055208 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 378880 4557495 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 379008 5497713 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 379136 10776066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 379136 5018494 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 379264 5757572 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 379392 36027012 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 379392 19962138 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 379392 9690177 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 379520 10271961 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 379648 16064874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 379648 7971895 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 379776 8092979 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 379904 77171542 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 379904 36908670 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 379904 18217042 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 379904 9161322 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 380032 9055720 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 380160 18691628 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 380160 10070387 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 380288 8621241 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 380416 40262872 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 380416 16334093 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 380416 6657438 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 380544 9676655 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 380672 23928779 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 380672 11858646 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 380800 12070133 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 380928 153148717 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 380928 117823378 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 380928 55259963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 380928 29498754 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 380928 15132010 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 380928 8013568 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 381056 7118442 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 381184 14366744 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 381184 8015898 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 381312 6350846 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 381440 25761209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 381440 11867281 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 381440 6713068 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 381568 5154213 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 381696 13893928 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 381696 6962503 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 381824 6931425 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 381952 62563415 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 381952 33531074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 381952 11816557 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 381952 4725065 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 382080 7091492 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 382208 21714517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 382208 11863449 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 382336 9851068 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 382464 29032341 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 382464 21292356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 382464 12080236 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 382592 9212120 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 382720 7739985 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 382720 5400080 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 382848 2339905 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 382976 35325339 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 382976 18059464 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 382976 12064683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 382976 7103139 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 382976 4845501 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 383104 2257638 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 383232 4961544 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 383232 2371644 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 383360 2589900 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 383488 5994781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 383488 4465542 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 383488 2448168 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 383616 2017374 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 383744 1529239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 383744 607164 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 383872 922075 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 384000 17265875 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 384000 11172909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 384000 5069054 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 384000 3528115 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 384128 1540939 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 384256 6103855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 384256 4033208 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 384384 2070647 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 384512 6092966 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 384512 3798689 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 384512 2488518 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 384640 1310171 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 384768 2294277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 384768 1255122 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 384896 1039155 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 385024 777903423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 385024 355432035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 385024 54440923 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 385024 21505681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 385024 8813676 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 385024 3312707 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 385024 724572 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 385152 2588135 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 385280 5500969 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 385280 3531933 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 385408 1969036 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 385536 12692005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 385536 3936030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 385536 1750613 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 385664 2185417 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 385792 8755975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 385792 5090041 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 385920 3665934 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 386048 32935242 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 386048 12028779 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 386048 7887909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 386048 4247644 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 386176 3640265 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 386304 4140870 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 386304 2761759 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 386432 1379111 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 386560 20906463 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 386560 2901640 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 386560 1528695 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 386688 1372945 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 386816 18004823 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 386816 7891262 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 386944 10113561 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 387072 300991112 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 387072 129023843 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 387072 53747543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 387072 23468166 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 387072 10319405 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 387200 13148761 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 387328 30279377 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 387328 14365311 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 387456 15914066 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 387584 75276300 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 387584 36927338 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 387584 19123109 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 387712 17804229 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 387840 38348962 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 387840 20432891 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 387968 17916071 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 388096 171967269 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 388096 78882559 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 388096 36893933 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 388096 18585260 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 388224 18308673 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 388352 41988626 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 388352 19224212 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 388480 22764414 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 388608 93084710 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 388608 49897922 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 388608 24964721 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 388736 24933201 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 388864 43186788 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 388864 22935049 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 388992 20251739 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 389120 422471388 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 389120 267186686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 389120 151906071 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 389120 69586915 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 389120 31825947 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 389120 16699211 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 389248 15126736 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 389376 37760968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 389376 18685751 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 389504 19075217 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 389632 82319156 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 389632 41546198 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 389632 20798314 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 389760 20747884 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 389888 40772958 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 389888 20510373 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 390016 20262585 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 390144 115280615 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 390144 68813046 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 390144 39523815 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 390144 19356503 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 390272 20167312 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 390400 29289231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 390400 15761022 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 390528 13528209 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 390656 46467569 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 390656 24740373 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 390656 12891709 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 390784 11848664 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 390912 21727196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 390912 11875528 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 391040 9851668 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 391168 155284702 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 391168 120536559 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 391168 53941534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 391168 20199517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 391168 9447129 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 391296 10752388 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 391424 33742017 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 391424 15085918 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 391552 18656099 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 391680 66595025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 391680 32401704 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 391680 17332930 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 391808 15068774 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 391936 34193321 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 391936 16354607 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 392064 17838714 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 392192 34748143 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 392192 28232880 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 392192 19174555 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 392192 12436107 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 392320 6738448 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 392448 9058325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 392448 4550288 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 392576 4508037 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 392704 6515263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 392704 3605012 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 392704 2444353 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 392832 1160659 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 392960 2910251 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 392960 1053431 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 393088 1856820 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 376832 (MobiusHarmonicTree.branch 1115317195 mobiusHarmonicBlock046 mobiusHarmonicBlock047) = true := Helfgott.combined

#print axioms solution
