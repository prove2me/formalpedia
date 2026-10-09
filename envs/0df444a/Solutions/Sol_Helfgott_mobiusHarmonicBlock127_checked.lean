-- Prove2me | solution 1 for Helfgott.mobiusHarmonicBlock127_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:10:49.730386+00:00
-- url     : https://prove2.me/submissions/3c6358e8-05b9-4b7f-ae6b-4bd593dc627b

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

private abbrev d7 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 0
private theorem p7 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040384 d7 = true := by decide +kernel

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 1
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040448 d8 = true := by decide +kernel

private def d6 : MobiusHarmonicTree := .branch 30231296 d7 d8
private abbrev d10 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 2
private theorem p10 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040512 d10 = true := by decide +kernel

private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 3
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040576 d11 = true := by decide +kernel

private def d9 : MobiusHarmonicTree := .branch 29399168 d10 d11
private def d5 : MobiusHarmonicTree := .branch 59630464 d6 d9
private abbrev d14 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 4
private theorem p14 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040640 d14 = true := by decide +kernel

private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 5
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040704 d15 = true := by decide +kernel

private def d13 : MobiusHarmonicTree := .branch 31031950 d14 d15
private abbrev d17 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 6
private theorem p17 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040768 d17 = true := by decide +kernel

private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 7
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040832 d18 = true := by decide +kernel

private def d16 : MobiusHarmonicTree := .branch 30719747 d17 d18
private def d12 : MobiusHarmonicTree := .branch 61751697 d13 d16
private def d4 : MobiusHarmonicTree := .branch 121382161 d5 d12
private abbrev d22 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 8
private theorem p22 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040896 d22 = true := by decide +kernel

private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 9
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040960 d23 = true := by decide +kernel

private def d21 : MobiusHarmonicTree := .branch 29366257 d22 d23
private abbrev d25 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 10
private theorem p25 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041024 d25 = true := by decide +kernel

private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 11
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041088 d26 = true := by decide +kernel

private def d24 : MobiusHarmonicTree := .branch 29248317 d25 d26
private def d20 : MobiusHarmonicTree := .branch 58614574 d21 d24
private abbrev d29 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 12
private theorem p29 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041152 d29 = true := by decide +kernel

private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 13
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041216 d30 = true := by decide +kernel

private def d28 : MobiusHarmonicTree := .branch 30426035 d29 d30
private abbrev d32 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 14
private theorem p32 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041280 d32 = true := by decide +kernel

private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 15
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041344 d33 = true := by decide +kernel

private def d31 : MobiusHarmonicTree := .branch 29002037 d32 d33
private def d27 : MobiusHarmonicTree := .branch 59428072 d28 d31
private def d19 : MobiusHarmonicTree := .branch 118042646 d20 d27
private def d3 : MobiusHarmonicTree := .branch 239424807 d4 d19
private abbrev d38 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 16
private theorem p38 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041408 d38 = true := by decide +kernel

private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 17
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041472 d39 = true := by decide +kernel

private def d37 : MobiusHarmonicTree := .branch 29696512 d38 d39
private abbrev d41 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 18
private theorem p41 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041536 d41 = true := by decide +kernel

private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 19
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041600 d42 = true := by decide +kernel

private def d40 : MobiusHarmonicTree := .branch 29552696 d41 d42
private def d36 : MobiusHarmonicTree := .branch 59249208 d37 d40
private abbrev d45 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 20
private theorem p45 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041664 d45 = true := by decide +kernel

private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 21
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041728 d46 = true := by decide +kernel

private def d44 : MobiusHarmonicTree := .branch 29039321 d45 d46
private abbrev d48 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 22
private theorem p48 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041792 d48 = true := by decide +kernel

private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 23
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041856 d49 = true := by decide +kernel

private def d47 : MobiusHarmonicTree := .branch 28542419 d48 d49
private def d43 : MobiusHarmonicTree := .branch 57581740 d44 d47
private def d35 : MobiusHarmonicTree := .branch 116830948 d36 d43
private abbrev d53 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 24
private theorem p53 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041920 d53 = true := by decide +kernel

private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 25
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1041984 d54 = true := by decide +kernel

private def d52 : MobiusHarmonicTree := .branch 29149268 d53 d54
private abbrev d56 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 26
private theorem p56 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042048 d56 = true := by decide +kernel

private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 27
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042112 d57 = true := by decide +kernel

private def d55 : MobiusHarmonicTree := .branch 28823299 d56 d57
private def d51 : MobiusHarmonicTree := .branch 57972567 d52 d55
private abbrev d60 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 28
private theorem p60 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042176 d60 = true := by decide +kernel

private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 29
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042240 d61 = true := by decide +kernel

private def d59 : MobiusHarmonicTree := .branch 27283634 d60 d61
private abbrev d63 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 30
private theorem p63 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042304 d63 = true := by decide +kernel

private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 31
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042368 d64 = true := by decide +kernel

private def d62 : MobiusHarmonicTree := .branch 26313263 d63 d64
private def d58 : MobiusHarmonicTree := .branch 53596897 d59 d62
private def d50 : MobiusHarmonicTree := .branch 111569464 d51 d58
private def d34 : MobiusHarmonicTree := .branch 228400412 d35 d50
private def d2 : MobiusHarmonicTree := .branch 467825219 d3 d34
private abbrev d70 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 32
private theorem p70 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042432 d70 = true := by decide +kernel

private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 33
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042496 d71 = true := by decide +kernel

private def d69 : MobiusHarmonicTree := .branch 25208779 d70 d71
private abbrev d73 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 34
private theorem p73 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042560 d73 = true := by decide +kernel

private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 35
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042624 d74 = true := by decide +kernel

private def d72 : MobiusHarmonicTree := .branch 26846761 d73 d74
private def d68 : MobiusHarmonicTree := .branch 52055540 d69 d72
private abbrev d77 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 36
private theorem p77 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042688 d77 = true := by decide +kernel

private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 37
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042752 d78 = true := by decide +kernel

private def d76 : MobiusHarmonicTree := .branch 27928086 d77 d78
private abbrev d80 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 38
private theorem p80 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042816 d80 = true := by decide +kernel

private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 39
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042880 d81 = true := by decide +kernel

private def d79 : MobiusHarmonicTree := .branch 28598764 d80 d81
private def d75 : MobiusHarmonicTree := .branch 56526850 d76 d79
private def d67 : MobiusHarmonicTree := .branch 108582390 d68 d75
private abbrev d85 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 40
private theorem p85 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1042944 d85 = true := by decide +kernel

private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 41
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043008 d86 = true := by decide +kernel

private def d84 : MobiusHarmonicTree := .branch 28461988 d85 d86
private abbrev d88 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 42
private theorem p88 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043072 d88 = true := by decide +kernel

private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 43
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043136 d89 = true := by decide +kernel

private def d87 : MobiusHarmonicTree := .branch 29517784 d88 d89
private def d83 : MobiusHarmonicTree := .branch 57979772 d84 d87
private abbrev d92 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 44
private theorem p92 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043200 d92 = true := by decide +kernel

private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 45
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043264 d93 = true := by decide +kernel

private def d91 : MobiusHarmonicTree := .branch 29895671 d92 d93
private abbrev d95 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 46
private theorem p95 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043328 d95 = true := by decide +kernel

private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 47
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043392 d96 = true := by decide +kernel

private def d94 : MobiusHarmonicTree := .branch 30626138 d95 d96
private def d90 : MobiusHarmonicTree := .branch 60521809 d91 d94
private def d82 : MobiusHarmonicTree := .branch 118501581 d83 d90
private def d66 : MobiusHarmonicTree := .branch 227083971 d67 d82
private abbrev d101 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 48
private theorem p101 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043456 d101 = true := by decide +kernel

private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 49
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043520 d102 = true := by decide +kernel

private def d100 : MobiusHarmonicTree := .branch 31614239 d101 d102
private abbrev d104 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 50
private theorem p104 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043584 d104 = true := by decide +kernel

private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 51
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043648 d105 = true := by decide +kernel

private def d103 : MobiusHarmonicTree := .branch 30714460 d104 d105
private def d99 : MobiusHarmonicTree := .branch 62328699 d100 d103
private abbrev d108 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 52
private theorem p108 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043712 d108 = true := by decide +kernel

private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 53
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043776 d109 = true := by decide +kernel

private def d107 : MobiusHarmonicTree := .branch 30411774 d108 d109
private abbrev d111 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 54
private theorem p111 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043840 d111 = true := by decide +kernel

private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 55
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043904 d112 = true := by decide +kernel

private def d110 : MobiusHarmonicTree := .branch 29244157 d111 d112
private def d106 : MobiusHarmonicTree := .branch 59655931 d107 d110
private def d98 : MobiusHarmonicTree := .branch 121984630 d99 d106
private abbrev d116 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 56
private theorem p116 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1043968 d116 = true := by decide +kernel

private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 57
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044032 d117 = true := by decide +kernel

private def d115 : MobiusHarmonicTree := .branch 30609269 d116 d117
private abbrev d119 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 58
private theorem p119 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044096 d119 = true := by decide +kernel

private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 59
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044160 d120 = true := by decide +kernel

private def d118 : MobiusHarmonicTree := .branch 32874346 d119 d120
private def d114 : MobiusHarmonicTree := .branch 63483615 d115 d118
private abbrev d123 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 60
private theorem p123 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044224 d123 = true := by decide +kernel

private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 61
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044288 d124 = true := by decide +kernel

private def d122 : MobiusHarmonicTree := .branch 31764316 d123 d124
private abbrev d126 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 62
private theorem p126 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044352 d126 = true := by decide +kernel

private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 63
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044416 d127 = true := by decide +kernel

private def d125 : MobiusHarmonicTree := .branch 30990591 d126 d127
private def d121 : MobiusHarmonicTree := .branch 62754907 d122 d125
private def d113 : MobiusHarmonicTree := .branch 126238522 d114 d121
private def d97 : MobiusHarmonicTree := .branch 248223152 d98 d113
private def d65 : MobiusHarmonicTree := .branch 475307123 d66 d97
private def d1 : MobiusHarmonicTree := .branch 943132342 d2 d65
private abbrev d134 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 64
private theorem p134 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044480 d134 = true := by decide +kernel

private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 65
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044544 d135 = true := by decide +kernel

private def d133 : MobiusHarmonicTree := .branch 32182547 d134 d135
private abbrev d137 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 66
private theorem p137 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044608 d137 = true := by decide +kernel

private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 67
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044672 d138 = true := by decide +kernel

private def d136 : MobiusHarmonicTree := .branch 31655934 d137 d138
private def d132 : MobiusHarmonicTree := .branch 63838481 d133 d136
private abbrev d141 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 68
private theorem p141 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044736 d141 = true := by decide +kernel

private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 69
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044800 d142 = true := by decide +kernel

private def d140 : MobiusHarmonicTree := .branch 31119920 d141 d142
private abbrev d144 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 70
private theorem p144 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044864 d144 = true := by decide +kernel

private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 71
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044928 d145 = true := by decide +kernel

private def d143 : MobiusHarmonicTree := .branch 30164839 d144 d145
private def d139 : MobiusHarmonicTree := .branch 61284759 d140 d143
private def d131 : MobiusHarmonicTree := .branch 125123240 d132 d139
private abbrev d149 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 72
private theorem p149 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1044992 d149 = true := by decide +kernel

private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 73
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045056 d150 = true := by decide +kernel

private def d148 : MobiusHarmonicTree := .branch 29868335 d149 d150
private abbrev d152 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 74
private theorem p152 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045120 d152 = true := by decide +kernel

private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 75
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045184 d153 = true := by decide +kernel

private def d151 : MobiusHarmonicTree := .branch 29880939 d152 d153
private def d147 : MobiusHarmonicTree := .branch 59749274 d148 d151
private abbrev d156 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 76
private theorem p156 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045248 d156 = true := by decide +kernel

private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 77
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045312 d157 = true := by decide +kernel

private def d155 : MobiusHarmonicTree := .branch 30837745 d156 d157
private abbrev d159 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 78
private theorem p159 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045376 d159 = true := by decide +kernel

private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 79
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045440 d160 = true := by decide +kernel

private def d158 : MobiusHarmonicTree := .branch 32375928 d159 d160
private def d154 : MobiusHarmonicTree := .branch 63213673 d155 d158
private def d146 : MobiusHarmonicTree := .branch 122962947 d147 d154
private def d130 : MobiusHarmonicTree := .branch 248086187 d131 d146
private abbrev d165 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 80
private theorem p165 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045504 d165 = true := by decide +kernel

private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 81
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045568 d166 = true := by decide +kernel

private def d164 : MobiusHarmonicTree := .branch 30883797 d165 d166
private abbrev d168 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 82
private theorem p168 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045632 d168 = true := by decide +kernel

private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 83
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045696 d169 = true := by decide +kernel

private def d167 : MobiusHarmonicTree := .branch 30048965 d168 d169
private def d163 : MobiusHarmonicTree := .branch 60932762 d164 d167
private abbrev d172 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 84
private theorem p172 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045760 d172 = true := by decide +kernel

private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 85
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045824 d173 = true := by decide +kernel

private def d171 : MobiusHarmonicTree := .branch 30119879 d172 d173
private abbrev d175 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 86
private theorem p175 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045888 d175 = true := by decide +kernel

private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 87
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1045952 d176 = true := by decide +kernel

private def d174 : MobiusHarmonicTree := .branch 31173591 d175 d176
private def d170 : MobiusHarmonicTree := .branch 61293470 d171 d174
private def d162 : MobiusHarmonicTree := .branch 122226232 d163 d170
private abbrev d180 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 88
private theorem p180 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046016 d180 = true := by decide +kernel

private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 89
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046080 d181 = true := by decide +kernel

private def d179 : MobiusHarmonicTree := .branch 30883954 d180 d181
private abbrev d183 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 90
private theorem p183 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046144 d183 = true := by decide +kernel

private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 91
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046208 d184 = true := by decide +kernel

private def d182 : MobiusHarmonicTree := .branch 32492664 d183 d184
private def d178 : MobiusHarmonicTree := .branch 63376618 d179 d182
private abbrev d187 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 92
private theorem p187 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046272 d187 = true := by decide +kernel

private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 93
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046336 d188 = true := by decide +kernel

private def d186 : MobiusHarmonicTree := .branch 32454275 d187 d188
private abbrev d190 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 94
private theorem p190 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046400 d190 = true := by decide +kernel

private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 95
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046464 d191 = true := by decide +kernel

private def d189 : MobiusHarmonicTree := .branch 33839730 d190 d191
private def d185 : MobiusHarmonicTree := .branch 66294005 d186 d189
private def d177 : MobiusHarmonicTree := .branch 129670623 d178 d185
private def d161 : MobiusHarmonicTree := .branch 251896855 d162 d177
private def d129 : MobiusHarmonicTree := .branch 499983042 d130 d161
private abbrev d197 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 96
private theorem p197 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046528 d197 = true := by decide +kernel

private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 97
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046592 d198 = true := by decide +kernel

private def d196 : MobiusHarmonicTree := .branch 34509236 d197 d198
private abbrev d200 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 98
private theorem p200 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046656 d200 = true := by decide +kernel

private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 99
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046720 d201 = true := by decide +kernel

private def d199 : MobiusHarmonicTree := .branch 34072235 d200 d201
private def d195 : MobiusHarmonicTree := .branch 68581471 d196 d199
private abbrev d204 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 100
private theorem p204 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046784 d204 = true := by decide +kernel

private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 101
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046848 d205 = true := by decide +kernel

private def d203 : MobiusHarmonicTree := .branch 34065196 d204 d205
private abbrev d207 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 102
private theorem p207 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046912 d207 = true := by decide +kernel

private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 103
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1046976 d208 = true := by decide +kernel

private def d206 : MobiusHarmonicTree := .branch 33998947 d207 d208
private def d202 : MobiusHarmonicTree := .branch 68064143 d203 d206
private def d194 : MobiusHarmonicTree := .branch 136645614 d195 d202
private abbrev d212 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 104
private theorem p212 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047040 d212 = true := by decide +kernel

private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 105
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047104 d213 = true := by decide +kernel

private def d211 : MobiusHarmonicTree := .branch 33314832 d212 d213
private abbrev d215 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 106
private theorem p215 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047168 d215 = true := by decide +kernel

private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 107
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047232 d216 = true := by decide +kernel

private def d214 : MobiusHarmonicTree := .branch 32814200 d215 d216
private def d210 : MobiusHarmonicTree := .branch 66129032 d211 d214
private abbrev d219 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 108
private theorem p219 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047296 d219 = true := by decide +kernel

private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 109
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047360 d220 = true := by decide +kernel

private def d218 : MobiusHarmonicTree := .branch 34064748 d219 d220
private abbrev d222 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 110
private theorem p222 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047424 d222 = true := by decide +kernel

private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 111
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047488 d223 = true := by decide +kernel

private def d221 : MobiusHarmonicTree := .branch 33847748 d222 d223
private def d217 : MobiusHarmonicTree := .branch 67912496 d218 d221
private def d209 : MobiusHarmonicTree := .branch 134041528 d210 d217
private def d193 : MobiusHarmonicTree := .branch 270687142 d194 d209
private abbrev d228 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 112
private theorem p228 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047552 d228 = true := by decide +kernel

private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 113
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047616 d229 = true := by decide +kernel

private def d227 : MobiusHarmonicTree := .branch 33013130 d228 d229
private abbrev d231 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 114
private theorem p231 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047680 d231 = true := by decide +kernel

private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 115
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047744 d232 = true := by decide +kernel

private def d230 : MobiusHarmonicTree := .branch 32133893 d231 d232
private def d226 : MobiusHarmonicTree := .branch 65147023 d227 d230
private abbrev d235 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 116
private theorem p235 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047808 d235 = true := by decide +kernel

private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 117
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047872 d236 = true := by decide +kernel

private def d234 : MobiusHarmonicTree := .branch 32116600 d235 d236
private abbrev d238 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 118
private theorem p238 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1047936 d238 = true := by decide +kernel

private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 119
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048000 d239 = true := by decide +kernel

private def d237 : MobiusHarmonicTree := .branch 31572612 d238 d239
private def d233 : MobiusHarmonicTree := .branch 63689212 d234 d237
private def d225 : MobiusHarmonicTree := .branch 128836235 d226 d233
private abbrev d243 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 120
private theorem p243 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048064 d243 = true := by decide +kernel

private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 121
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048128 d244 = true := by decide +kernel

private def d242 : MobiusHarmonicTree := .branch 32088684 d243 d244
private abbrev d246 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 122
private theorem p246 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048192 d246 = true := by decide +kernel

private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 123
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048256 d247 = true := by decide +kernel

private def d245 : MobiusHarmonicTree := .branch 32646702 d246 d247
private def d241 : MobiusHarmonicTree := .branch 64735386 d242 d245
private abbrev d250 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 124
private theorem p250 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048320 d250 = true := by decide +kernel

private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 125
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048384 d251 = true := by decide +kernel

private def d249 : MobiusHarmonicTree := .branch 32104728 d250 d251
private abbrev d253 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 126
private theorem p253 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048448 d253 = true := by decide +kernel

private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock127 127
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1048512 d254 = true := by decide +kernel

private def d252 : MobiusHarmonicTree := .branch 32249599 d253 d254
private def d248 : MobiusHarmonicTree := .branch 64354327 d249 d252
private def d240 : MobiusHarmonicTree := .branch 129089713 d241 d248
private def d224 : MobiusHarmonicTree := .branch 257925948 d225 d240
private def d192 : MobiusHarmonicTree := .branch 528613090 d193 d224
private def d128 : MobiusHarmonicTree := .branch 1028596132 d129 d192
private def d0 : MobiusHarmonicTree := .branch 1971728474 d1 d128

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 8 1040384 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 1040384 1971728474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1040384 943132342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1040384 467825219 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1040384 239424807 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1040384 121382161 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1040384 59630464 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1040384 30231296 _ _ (by decide) p7 p8 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1040512 29399168 _ _ (by decide) p10 p11 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1040640 61751697 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1040640 31031950 _ _ (by decide) p14 p15 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1040768 30719747 _ _ (by decide) p17 p18 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1040896 118042646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1040896 58614574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1040896 29366257 _ _ (by decide) p22 p23 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1041024 29248317 _ _ (by decide) p25 p26 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1041152 59428072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1041152 30426035 _ _ (by decide) p29 p30 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1041280 29002037 _ _ (by decide) p32 p33 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1041408 228400412 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1041408 116830948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1041408 59249208 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1041408 29696512 _ _ (by decide) p38 p39 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1041536 29552696 _ _ (by decide) p41 p42 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1041664 57581740 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1041664 29039321 _ _ (by decide) p45 p46 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1041792 28542419 _ _ (by decide) p48 p49 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1041920 111569464 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1041920 57972567 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1041920 29149268 _ _ (by decide) p53 p54 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1042048 28823299 _ _ (by decide) p56 p57 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1042176 53596897 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1042176 27283634 _ _ (by decide) p60 p61 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1042304 26313263 _ _ (by decide) p63 p64 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1042432 475307123 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1042432 227083971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1042432 108582390 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1042432 52055540 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1042432 25208779 _ _ (by decide) p70 p71 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1042560 26846761 _ _ (by decide) p73 p74 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1042688 56526850 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1042688 27928086 _ _ (by decide) p77 p78 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1042816 28598764 _ _ (by decide) p80 p81 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1042944 118501581 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1042944 57979772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1042944 28461988 _ _ (by decide) p85 p86 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1043072 29517784 _ _ (by decide) p88 p89 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1043200 60521809 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1043200 29895671 _ _ (by decide) p92 p93 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1043328 30626138 _ _ (by decide) p95 p96 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1043456 248223152 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1043456 121984630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1043456 62328699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1043456 31614239 _ _ (by decide) p101 p102 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1043584 30714460 _ _ (by decide) p104 p105 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1043712 59655931 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1043712 30411774 _ _ (by decide) p108 p109 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1043840 29244157 _ _ (by decide) p111 p112 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1043968 126238522 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1043968 63483615 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1043968 30609269 _ _ (by decide) p116 p117 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1044096 32874346 _ _ (by decide) p119 p120 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1044224 62754907 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1044224 31764316 _ _ (by decide) p123 p124 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1044352 30990591 _ _ (by decide) p126 p127 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1044480 1028596132 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1044480 499983042 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1044480 248086187 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1044480 125123240 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1044480 63838481 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1044480 32182547 _ _ (by decide) p134 p135 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1044608 31655934 _ _ (by decide) p137 p138 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1044736 61284759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1044736 31119920 _ _ (by decide) p141 p142 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1044864 30164839 _ _ (by decide) p144 p145 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1044992 122962947 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1044992 59749274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1044992 29868335 _ _ (by decide) p149 p150 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1045120 29880939 _ _ (by decide) p152 p153 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1045248 63213673 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1045248 30837745 _ _ (by decide) p156 p157 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1045376 32375928 _ _ (by decide) p159 p160 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1045504 251896855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1045504 122226232 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1045504 60932762 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1045504 30883797 _ _ (by decide) p165 p166 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1045632 30048965 _ _ (by decide) p168 p169 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1045760 61293470 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1045760 30119879 _ _ (by decide) p172 p173 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1045888 31173591 _ _ (by decide) p175 p176 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1046016 129670623 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1046016 63376618 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1046016 30883954 _ _ (by decide) p180 p181 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1046144 32492664 _ _ (by decide) p183 p184 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1046272 66294005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1046272 32454275 _ _ (by decide) p187 p188 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1046400 33839730 _ _ (by decide) p190 p191 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1046528 528613090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1046528 270687142 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1046528 136645614 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1046528 68581471 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1046528 34509236 _ _ (by decide) p197 p198 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1046656 34072235 _ _ (by decide) p200 p201 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1046784 68064143 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1046784 34065196 _ _ (by decide) p204 p205 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1046912 33998947 _ _ (by decide) p207 p208 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1047040 134041528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1047040 66129032 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1047040 33314832 _ _ (by decide) p212 p213 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1047168 32814200 _ _ (by decide) p215 p216 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1047296 67912496 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1047296 34064748 _ _ (by decide) p219 p220 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1047424 33847748 _ _ (by decide) p222 p223 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1047552 257925948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1047552 128836235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1047552 65147023 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1047552 33013130 _ _ (by decide) p228 p229 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1047680 32133893 _ _ (by decide) p231 p232 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1047808 63689212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1047808 32116600 _ _ (by decide) p235 p236 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1047936 31572612 _ _ (by decide) p238 p239 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1048064 129089713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1048064 64735386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1048064 32088684 _ _ (by decide) p243 p244 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1048192 32646702 _ _ (by decide) p246 p247 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1048320 64354327 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1048320 32104728 _ _ (by decide) p250 p251 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1048448 32249599 _ _ (by decide) p253 p254 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 8 1040384 mobiusHarmonicBlock127 = true := Helfgott.combined

#print axioms solution
