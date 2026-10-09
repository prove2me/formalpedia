-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair017_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:56:05.351983+00:00
-- url     : https://prove2.me/submissions/34bb8537-dc03-41d8-8e7c-aaa8eaff93b3

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278528 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278592 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 5491770 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278656 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278720 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 4423835 d11 d12
private def d6 : MobiusHarmonicTree := .branch 9915605 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278784 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278848 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 5436832 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278912 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278976 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 4294229 d18 d19
private def d13 : MobiusHarmonicTree := .branch 9731061 d14 d17
private def d5 : MobiusHarmonicTree := .branch 19646666 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279040 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279104 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 6162588 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279168 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279232 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 5525801 d26 d27
private def d21 : MobiusHarmonicTree := .branch 11688389 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279296 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279360 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 9038580 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279424 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279488 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 10730274 d33 d34
private def d28 : MobiusHarmonicTree := .branch 19768854 d29 d32
private def d20 : MobiusHarmonicTree := .branch 31457243 d21 d28
private def d4 : MobiusHarmonicTree := .branch 51103909 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279552 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279616 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 10750682 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279680 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279744 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 13530109 d42 d43
private def d37 : MobiusHarmonicTree := .branch 24280791 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279808 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279872 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 15778727 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 279936 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280000 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 20492776 d49 d50
private def d44 : MobiusHarmonicTree := .branch 36271503 d45 d48
private def d36 : MobiusHarmonicTree := .branch 60552294 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280064 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280128 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 20401517 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280192 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280256 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 17334422 d57 d58
private def d52 : MobiusHarmonicTree := .branch 37735939 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280320 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280384 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 15321765 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280448 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280512 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 19564401 d64 d65
private def d59 : MobiusHarmonicTree := .branch 34886166 d60 d63
private def d51 : MobiusHarmonicTree := .branch 72622105 d52 d59
private def d35 : MobiusHarmonicTree := .branch 133174399 d36 d51
private def d3 : MobiusHarmonicTree := .branch 184278308 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280576 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280640 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 13587043 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280704 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280768 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 13541195 d74 d75
private def d69 : MobiusHarmonicTree := .branch 27128238 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280832 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280896 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 21039953 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 280960 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281024 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 16440070 d81 d82
private def d76 : MobiusHarmonicTree := .branch 37480023 d77 d80
private def d68 : MobiusHarmonicTree := .branch 64608261 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281088 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281152 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 19725984 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281216 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281280 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 19866414 d89 d90
private def d84 : MobiusHarmonicTree := .branch 39592398 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281344 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281408 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 20425962 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281472 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281536 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 22778785 d96 d97
private def d91 : MobiusHarmonicTree := .branch 43204747 d92 d95
private def d83 : MobiusHarmonicTree := .branch 82797145 d84 d91
private def d67 : MobiusHarmonicTree := .branch 147405406 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281600 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281664 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 19896242 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281728 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281792 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 19152509 d105 d106
private def d100 : MobiusHarmonicTree := .branch 39048751 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281856 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281920 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 19927738 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 281984 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282048 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 20145746 d112 d113
private def d107 : MobiusHarmonicTree := .branch 40073484 d108 d111
private def d99 : MobiusHarmonicTree := .branch 79122235 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282112 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282176 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 18559187 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282240 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282304 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 18313788 d120 d121
private def d115 : MobiusHarmonicTree := .branch 36872975 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282368 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282432 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 20089747 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282496 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282560 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 23177663 d127 d128
private def d122 : MobiusHarmonicTree := .branch 43267410 d123 d126
private def d114 : MobiusHarmonicTree := .branch 80140385 d115 d122
private def d98 : MobiusHarmonicTree := .branch 159262620 d99 d114
private def d66 : MobiusHarmonicTree := .branch 306668026 d67 d98
private def d2 : MobiusHarmonicTree := .branch 490946334 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282624 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282688 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 25292897 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282752 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282816 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 24740798 d138 d139
private def d133 : MobiusHarmonicTree := .branch 50033695 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282880 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 282944 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 20788670 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283008 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283072 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 21009072 d145 d146
private def d140 : MobiusHarmonicTree := .branch 41797742 d141 d144
private def d132 : MobiusHarmonicTree := .branch 91831437 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283136 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283200 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 19438351 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283264 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283328 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 30014202 d153 d154
private def d148 : MobiusHarmonicTree := .branch 49452553 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283392 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283456 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 40846099 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283520 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283584 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 38789199 d160 d161
private def d155 : MobiusHarmonicTree := .branch 79635298 d156 d159
private def d147 : MobiusHarmonicTree := .branch 129087851 d148 d155
private def d131 : MobiusHarmonicTree := .branch 220919288 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283648 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283712 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 45581353 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283776 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283840 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 43292164 d169 d170
private def d164 : MobiusHarmonicTree := .branch 88873517 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283904 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 283968 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 48368250 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284032 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284096 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 48276075 d176 d177
private def d171 : MobiusHarmonicTree := .branch 96644325 d172 d175
private def d163 : MobiusHarmonicTree := .branch 185517842 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284160 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284224 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 45204096 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284288 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284352 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 42032344 d184 d185
private def d179 : MobiusHarmonicTree := .branch 87236440 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284416 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284480 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 40734132 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284544 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284608 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 38249449 d191 d192
private def d186 : MobiusHarmonicTree := .branch 78983581 d187 d190
private def d178 : MobiusHarmonicTree := .branch 166220021 d179 d186
private def d162 : MobiusHarmonicTree := .branch 351737863 d163 d178
private def d130 : MobiusHarmonicTree := .branch 572657151 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284672 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284736 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 30930684 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284800 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284864 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 30919880 d201 d202
private def d196 : MobiusHarmonicTree := .branch 61850564 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284928 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 284992 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 34222093 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285056 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285120 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 34157789 d208 d209
private def d203 : MobiusHarmonicTree := .branch 68379882 d204 d207
private def d195 : MobiusHarmonicTree := .branch 130230446 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285184 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285248 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 35379778 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285312 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285376 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 37441854 d216 d217
private def d211 : MobiusHarmonicTree := .branch 72821632 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285440 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285504 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 36087289 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285568 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285632 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 34733646 d223 d224
private def d218 : MobiusHarmonicTree := .branch 70820935 d219 d222
private def d210 : MobiusHarmonicTree := .branch 143642567 d211 d218
private def d194 : MobiusHarmonicTree := .branch 273873013 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285696 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285760 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 36285666 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285824 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285888 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 36511041 d232 d233
private def d227 : MobiusHarmonicTree := .branch 72796707 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 285952 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286016 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 38047059 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286080 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286144 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 34297472 d239 d240
private def d234 : MobiusHarmonicTree := .branch 72344531 d235 d238
private def d226 : MobiusHarmonicTree := .branch 145141238 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286208 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286272 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 36807736 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286336 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286400 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 39151473 d247 d248
private def d242 : MobiusHarmonicTree := .branch 75959209 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286464 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286528 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 41461935 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286592 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock034 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286656 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 41098368 d254 d255
private def d249 : MobiusHarmonicTree := .branch 82560303 d250 d253
private def d241 : MobiusHarmonicTree := .branch 158519512 d242 d249
private def d225 : MobiusHarmonicTree := .branch 303660750 d226 d241
private def d193 : MobiusHarmonicTree := .branch 577533763 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1150190914 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1641137248 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286720 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286784 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 34866418 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286848 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286912 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 33247023 d266 d267
private def d261 : MobiusHarmonicTree := .branch 68113441 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 286976 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287040 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 37799725 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287104 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287168 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 37876883 d273 d274
private def d268 : MobiusHarmonicTree := .branch 75676608 d269 d272
private def d260 : MobiusHarmonicTree := .branch 143790049 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287232 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287296 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 36506015 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287360 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287424 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 41280339 d281 d282
private def d276 : MobiusHarmonicTree := .branch 77786354 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287488 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287552 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 40086895 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287616 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287680 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 42203284 d288 d289
private def d283 : MobiusHarmonicTree := .branch 82290179 d284 d287
private def d275 : MobiusHarmonicTree := .branch 160076533 d276 d283
private def d259 : MobiusHarmonicTree := .branch 303866582 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287744 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287808 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 46082815 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287872 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 287936 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 46808946 d297 d298
private def d292 : MobiusHarmonicTree := .branch 92891761 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288000 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288064 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 52405203 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288128 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288192 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 49575031 d304 d305
private def d299 : MobiusHarmonicTree := .branch 101980234 d300 d303
private def d291 : MobiusHarmonicTree := .branch 194871995 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288256 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288320 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 45963058 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288384 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288448 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 41380305 d312 d313
private def d307 : MobiusHarmonicTree := .branch 87343363 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288512 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288576 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 42751262 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288640 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288704 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 50688540 d319 d320
private def d314 : MobiusHarmonicTree := .branch 93439802 d315 d318
private def d306 : MobiusHarmonicTree := .branch 180783165 d307 d314
private def d290 : MobiusHarmonicTree := .branch 375655160 d291 d306
private def d258 : MobiusHarmonicTree := .branch 679521742 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288768 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288832 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 55052765 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288896 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 288960 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 59091440 d329 d330
private def d324 : MobiusHarmonicTree := .branch 114144205 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289024 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289088 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 55374527 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289152 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289216 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 48915266 d336 d337
private def d331 : MobiusHarmonicTree := .branch 104289793 d332 d335
private def d323 : MobiusHarmonicTree := .branch 218433998 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289280 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289344 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 47822090 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289408 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289472 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 49365747 d344 d345
private def d339 : MobiusHarmonicTree := .branch 97187837 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289536 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289600 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 49175065 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289664 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289728 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 49429354 d351 d352
private def d346 : MobiusHarmonicTree := .branch 98604419 d347 d350
private def d338 : MobiusHarmonicTree := .branch 195792256 d339 d346
private def d322 : MobiusHarmonicTree := .branch 414226254 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289792 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289856 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 48203628 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289920 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 289984 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 43223451 d360 d361
private def d355 : MobiusHarmonicTree := .branch 91427079 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290048 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290112 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 39336597 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290176 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290240 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 39560304 d367 d368
private def d362 : MobiusHarmonicTree := .branch 78896901 d363 d366
private def d354 : MobiusHarmonicTree := .branch 170323980 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290304 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290368 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 43117798 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290432 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290496 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 41543051 d375 d376
private def d370 : MobiusHarmonicTree := .branch 84660849 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290560 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290624 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 41541893 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290688 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290752 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 41795123 d382 d383
private def d377 : MobiusHarmonicTree := .branch 83337016 d378 d381
private def d369 : MobiusHarmonicTree := .branch 167997865 d370 d377
private def d353 : MobiusHarmonicTree := .branch 338321845 d354 d369
private def d321 : MobiusHarmonicTree := .branch 752548099 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1432069841 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290816 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290880 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 41886930 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 290944 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291008 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 42390737 d393 d394
private def d388 : MobiusHarmonicTree := .branch 84277667 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291072 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291136 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 45899511 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291200 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291264 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 46116381 d400 d401
private def d395 : MobiusHarmonicTree := .branch 92015892 d396 d399
private def d387 : MobiusHarmonicTree := .branch 176293559 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291328 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291392 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 44370063 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291456 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291520 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 42858370 d408 d409
private def d403 : MobiusHarmonicTree := .branch 87228433 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291584 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291648 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 43161680 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291712 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291776 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 43149624 d415 d416
private def d410 : MobiusHarmonicTree := .branch 86311304 d411 d414
private def d402 : MobiusHarmonicTree := .branch 173539737 d403 d410
private def d386 : MobiusHarmonicTree := .branch 349833296 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291840 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291904 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 43647904 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 291968 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292032 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 42916876 d424 d425
private def d419 : MobiusHarmonicTree := .branch 86564780 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292096 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292160 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 47620984 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292224 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292288 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 49331629 d431 d432
private def d426 : MobiusHarmonicTree := .branch 96952613 d427 d430
private def d418 : MobiusHarmonicTree := .branch 183517393 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292352 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292416 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 47860125 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292480 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292544 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 45371208 d439 d440
private def d434 : MobiusHarmonicTree := .branch 93231333 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292608 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292672 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 43024554 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292736 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292800 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 42483189 d446 d447
private def d441 : MobiusHarmonicTree := .branch 85507743 d442 d445
private def d433 : MobiusHarmonicTree := .branch 178739076 d434 d441
private def d417 : MobiusHarmonicTree := .branch 362256469 d418 d433
private def d385 : MobiusHarmonicTree := .branch 712089765 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292864 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292928 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 39173687 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 292992 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293056 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 43933333 d456 d457
private def d451 : MobiusHarmonicTree := .branch 83107020 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293120 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293184 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 42393507 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293248 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293312 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 37676626 d463 d464
private def d458 : MobiusHarmonicTree := .branch 80070133 d459 d462
private def d450 : MobiusHarmonicTree := .branch 163177153 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293376 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293440 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 41654377 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293504 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293568 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 43083616 d471 d472
private def d466 : MobiusHarmonicTree := .branch 84737993 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293632 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293696 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 49360435 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293760 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293824 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 52078751 d478 d479
private def d473 : MobiusHarmonicTree := .branch 101439186 d474 d477
private def d465 : MobiusHarmonicTree := .branch 186177179 d466 d473
private def d449 : MobiusHarmonicTree := .branch 349354332 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293888 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 293952 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 53665302 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294016 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294080 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 53733836 d487 d488
private def d482 : MobiusHarmonicTree := .branch 107399138 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294144 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294208 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 51124190 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294272 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294336 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 42135750 d494 d495
private def d489 : MobiusHarmonicTree := .branch 93259940 d490 d493
private def d481 : MobiusHarmonicTree := .branch 200659078 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294400 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294464 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 46086986 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294528 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294592 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 55038457 d502 d503
private def d497 : MobiusHarmonicTree := .branch 101125443 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294656 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294720 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 62367806 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294784 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock035 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294848 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 59814093 d509 d510
private def d504 : MobiusHarmonicTree := .branch 122181899 d505 d508
private def d496 : MobiusHarmonicTree := .branch 223307342 d497 d504
private def d480 : MobiusHarmonicTree := .branch 423966420 d481 d496
private def d448 : MobiusHarmonicTree := .branch 773320752 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1485410517 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2917480358 d257 d384
private def d0 : MobiusHarmonicTree := .branch 4558617606 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 278528 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 278528 4558617606 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 278528 1641137248 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 278528 490946334 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 278528 184278308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 278528 51103909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 278528 19646666 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 278528 9915605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 278528 5491770 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 278656 4423835 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 278784 9731061 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 278784 5436832 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 278912 4294229 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 279040 31457243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 279040 11688389 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 279040 6162588 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 279168 5525801 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 279296 19768854 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 279296 9038580 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 279424 10730274 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 279552 133174399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 279552 60552294 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 279552 24280791 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 279552 10750682 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 279680 13530109 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 279808 36271503 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 279808 15778727 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 279936 20492776 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 280064 72622105 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 280064 37735939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 280064 20401517 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 280192 17334422 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 280320 34886166 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 280320 15321765 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 280448 19564401 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 280576 306668026 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 280576 147405406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 280576 64608261 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 280576 27128238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 280576 13587043 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 280704 13541195 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 280832 37480023 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 280832 21039953 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 280960 16440070 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 281088 82797145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 281088 39592398 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 281088 19725984 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 281216 19866414 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 281344 43204747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 281344 20425962 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 281472 22778785 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 281600 159262620 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 281600 79122235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 281600 39048751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 281600 19896242 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 281728 19152509 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 281856 40073484 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 281856 19927738 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 281984 20145746 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 282112 80140385 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 282112 36872975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 282112 18559187 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 282240 18313788 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 282368 43267410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 282368 20089747 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 282496 23177663 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 282624 1150190914 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 282624 572657151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 282624 220919288 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 282624 91831437 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 282624 50033695 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 282624 25292897 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 282752 24740798 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 282880 41797742 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 282880 20788670 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 283008 21009072 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 283136 129087851 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 283136 49452553 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 283136 19438351 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 283264 30014202 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 283392 79635298 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 283392 40846099 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 283520 38789199 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 283648 351737863 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 283648 185517842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 283648 88873517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 283648 45581353 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 283776 43292164 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 283904 96644325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 283904 48368250 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 284032 48276075 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 284160 166220021 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 284160 87236440 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 284160 45204096 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 284288 42032344 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 284416 78983581 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 284416 40734132 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 284544 38249449 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 284672 577533763 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 284672 273873013 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 284672 130230446 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 284672 61850564 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 284672 30930684 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 284800 30919880 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 284928 68379882 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 284928 34222093 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 285056 34157789 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 285184 143642567 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 285184 72821632 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 285184 35379778 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 285312 37441854 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 285440 70820935 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 285440 36087289 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 285568 34733646 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 285696 303660750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 285696 145141238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 285696 72796707 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 285696 36285666 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 285824 36511041 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 285952 72344531 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 285952 38047059 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 286080 34297472 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 286208 158519512 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 286208 75959209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 286208 36807736 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 286336 39151473 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 286464 82560303 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 286464 41461935 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 286592 41098368 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 286720 2917480358 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 286720 1432069841 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 286720 679521742 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 286720 303866582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 286720 143790049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 286720 68113441 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 286720 34866418 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 286848 33247023 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 286976 75676608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 286976 37799725 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 287104 37876883 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 287232 160076533 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 287232 77786354 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 287232 36506015 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 287360 41280339 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 287488 82290179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 287488 40086895 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 287616 42203284 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 287744 375655160 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 287744 194871995 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 287744 92891761 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 287744 46082815 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 287872 46808946 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 288000 101980234 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 288000 52405203 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 288128 49575031 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 288256 180783165 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 288256 87343363 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 288256 45963058 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 288384 41380305 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 288512 93439802 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 288512 42751262 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 288640 50688540 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 288768 752548099 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 288768 414226254 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 288768 218433998 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 288768 114144205 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 288768 55052765 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 288896 59091440 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 289024 104289793 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 289024 55374527 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 289152 48915266 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 289280 195792256 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 289280 97187837 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 289280 47822090 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 289408 49365747 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 289536 98604419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 289536 49175065 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 289664 49429354 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 289792 338321845 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 289792 170323980 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 289792 91427079 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 289792 48203628 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 289920 43223451 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 290048 78896901 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 290048 39336597 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 290176 39560304 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 290304 167997865 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 290304 84660849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 290304 43117798 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 290432 41543051 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 290560 83337016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 290560 41541893 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 290688 41795123 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 290816 1485410517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 290816 712089765 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 290816 349833296 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 290816 176293559 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 290816 84277667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 290816 41886930 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 290944 42390737 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 291072 92015892 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 291072 45899511 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 291200 46116381 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 291328 173539737 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 291328 87228433 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 291328 44370063 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 291456 42858370 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 291584 86311304 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 291584 43161680 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 291712 43149624 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 291840 362256469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 291840 183517393 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 291840 86564780 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 291840 43647904 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 291968 42916876 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 292096 96952613 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 292096 47620984 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 292224 49331629 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 292352 178739076 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 292352 93231333 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 292352 47860125 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 292480 45371208 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 292608 85507743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 292608 43024554 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 292736 42483189 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 292864 773320752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 292864 349354332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 292864 163177153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 292864 83107020 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 292864 39173687 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 292992 43933333 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 293120 80070133 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 293120 42393507 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 293248 37676626 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 293376 186177179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 293376 84737993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 293376 41654377 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 293504 43083616 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 293632 101439186 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 293632 49360435 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 293760 52078751 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 293888 423966420 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 293888 200659078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 293888 107399138 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 293888 53665302 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 294016 53733836 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 294144 93259940 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 294144 51124190 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 294272 42135750 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 294400 223307342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 294400 101125443 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 294400 46086986 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 294528 55038457 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 294656 122181899 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 294656 62367806 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 294784 59814093 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 278528 (MobiusHarmonicTree.branch 4558617606 mobiusHarmonicBlock034 mobiusHarmonicBlock035) = true := Helfgott.combined

#print axioms solution
