-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair005_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:08:37.214708+00:00
-- url     : https://prove2.me/submissions/5a16f192-f7f6-4469-b380-01ba721b3743

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81920 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81984 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 43518159 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82048 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82112 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 55326381 d11 d12
private def d6 : MobiusHarmonicTree := .branch 98844540 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82176 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82240 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 76251859 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82304 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82368 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 91515555 d18 d19
private def d13 : MobiusHarmonicTree := .branch 167767414 d14 d17
private def d5 : MobiusHarmonicTree := .branch 266611954 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82432 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82496 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 84041436 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82560 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82624 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 87167816 d26 d27
private def d21 : MobiusHarmonicTree := .branch 171209252 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82688 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82752 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 80433849 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82816 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82880 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 81841598 d33 d34
private def d28 : MobiusHarmonicTree := .branch 162275447 d29 d32
private def d20 : MobiusHarmonicTree := .branch 333484699 d21 d28
private def d4 : MobiusHarmonicTree := .branch 600096653 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 82944 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83008 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 80740167 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83072 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83136 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 66411123 d42 d43
private def d37 : MobiusHarmonicTree := .branch 147151290 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83200 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83264 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 55079130 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83328 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83392 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 46383325 d49 d50
private def d44 : MobiusHarmonicTree := .branch 101462455 d45 d48
private def d36 : MobiusHarmonicTree := .branch 248613745 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83456 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83520 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 37011909 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83584 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83648 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 39439256 d57 d58
private def d52 : MobiusHarmonicTree := .branch 76451165 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83712 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83776 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 27361988 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83840 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83904 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 9235973 d64 d65
private def d59 : MobiusHarmonicTree := .branch 36597961 d60 d63
private def d51 : MobiusHarmonicTree := .branch 113049126 d52 d59
private def d35 : MobiusHarmonicTree := .branch 361662871 d36 d51
private def d3 : MobiusHarmonicTree := .branch 961759524 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 83968 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84032 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 6796433 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84096 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84160 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 7068508 d74 d75
private def d69 : MobiusHarmonicTree := .branch 13864941 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84224 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84288 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 7937351 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84352 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84416 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 3742921 d81 d82
private def d76 : MobiusHarmonicTree := .branch 11680272 d77 d80
private def d68 : MobiusHarmonicTree := .branch 25545213 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84480 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84544 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 9700277 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84608 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84672 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 4923506 d89 d90
private def d84 : MobiusHarmonicTree := .branch 14623783 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84736 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84800 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 17580040 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84864 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84928 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 37064695 d96 d97
private def d91 : MobiusHarmonicTree := .branch 54644735 d92 d95
private def d83 : MobiusHarmonicTree := .branch 69268518 d84 d91
private def d67 : MobiusHarmonicTree := .branch 94813731 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 84992 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85056 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 32732948 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85120 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85184 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 37611722 d105 d106
private def d100 : MobiusHarmonicTree := .branch 70344670 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85248 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85312 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 31530771 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85376 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85440 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 39418536 d112 d113
private def d107 : MobiusHarmonicTree := .branch 70949307 d108 d111
private def d99 : MobiusHarmonicTree := .branch 141293977 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85504 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85568 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 49737918 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85632 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85696 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 57807914 d120 d121
private def d115 : MobiusHarmonicTree := .branch 107545832 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85760 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85824 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 72459968 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85888 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 85952 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 89491150 d127 d128
private def d122 : MobiusHarmonicTree := .branch 161951118 d123 d126
private def d114 : MobiusHarmonicTree := .branch 269496950 d115 d122
private def d98 : MobiusHarmonicTree := .branch 410790927 d99 d114
private def d66 : MobiusHarmonicTree := .branch 505604658 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1467364182 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86016 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86080 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 90731074 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86144 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86208 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 78220511 d138 d139
private def d133 : MobiusHarmonicTree := .branch 168951585 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86272 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86336 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 65016455 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86400 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86464 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 48288249 d145 d146
private def d140 : MobiusHarmonicTree := .branch 113304704 d141 d144
private def d132 : MobiusHarmonicTree := .branch 282256289 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86528 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86592 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 47346510 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86656 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86720 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 59399748 d153 d154
private def d148 : MobiusHarmonicTree := .branch 106746258 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86784 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86848 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 55892249 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86912 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 86976 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 51682967 d160 d161
private def d155 : MobiusHarmonicTree := .branch 107575216 d156 d159
private def d147 : MobiusHarmonicTree := .branch 214321474 d148 d155
private def d131 : MobiusHarmonicTree := .branch 496577763 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87040 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87104 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 50364483 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87168 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87232 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 56747268 d169 d170
private def d164 : MobiusHarmonicTree := .branch 107111751 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87296 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87360 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 43418692 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87424 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87488 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 52051570 d176 d177
private def d171 : MobiusHarmonicTree := .branch 95470262 d172 d175
private def d163 : MobiusHarmonicTree := .branch 202582013 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87552 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87616 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 58404176 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87680 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87744 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 37862563 d184 d185
private def d179 : MobiusHarmonicTree := .branch 96266739 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87808 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87872 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 31989506 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 87936 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88000 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 34910385 d191 d192
private def d186 : MobiusHarmonicTree := .branch 66899891 d187 d190
private def d178 : MobiusHarmonicTree := .branch 163166630 d179 d186
private def d162 : MobiusHarmonicTree := .branch 365748643 d163 d178
private def d130 : MobiusHarmonicTree := .branch 862326406 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88064 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88128 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 45533113 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88192 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88256 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 60812376 d201 d202
private def d196 : MobiusHarmonicTree := .branch 106345489 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88320 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88384 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 64502752 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88448 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88512 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 64918976 d208 d209
private def d203 : MobiusHarmonicTree := .branch 129421728 d204 d207
private def d195 : MobiusHarmonicTree := .branch 235767217 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88576 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88640 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 60968812 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88704 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88768 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 67028694 d216 d217
private def d211 : MobiusHarmonicTree := .branch 127997506 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88832 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88896 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 49768872 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 88960 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89024 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 37979902 d223 d224
private def d218 : MobiusHarmonicTree := .branch 87748774 d219 d222
private def d210 : MobiusHarmonicTree := .branch 215746280 d211 d218
private def d194 : MobiusHarmonicTree := .branch 451513497 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89088 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89152 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 28882200 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89216 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89280 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 34308267 d232 d233
private def d227 : MobiusHarmonicTree := .branch 63190467 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89344 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89408 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 33252882 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89472 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89536 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 17771639 d239 d240
private def d234 : MobiusHarmonicTree := .branch 51024521 d235 d238
private def d226 : MobiusHarmonicTree := .branch 114214988 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89600 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89664 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 10629911 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89728 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89792 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 7260554 d247 d248
private def d242 : MobiusHarmonicTree := .branch 17890465 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89856 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89920 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 18281601 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 89984 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock010 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90048 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 9829119 d254 d255
private def d249 : MobiusHarmonicTree := .branch 28110720 d250 d253
private def d241 : MobiusHarmonicTree := .branch 46001185 d242 d249
private def d225 : MobiusHarmonicTree := .branch 160216173 d226 d241
private def d193 : MobiusHarmonicTree := .branch 611729670 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1474056076 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2941420258 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90112 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90176 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 11964161 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90240 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90304 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 9259229 d266 d267
private def d261 : MobiusHarmonicTree := .branch 21223390 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90368 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90432 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 3771532 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90496 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90560 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 4945694 d273 d274
private def d268 : MobiusHarmonicTree := .branch 8717226 d269 d272
private def d260 : MobiusHarmonicTree := .branch 29940616 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90624 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90688 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 14741401 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90752 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90816 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 22497334 d281 d282
private def d276 : MobiusHarmonicTree := .branch 37238735 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90880 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 90944 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 17977798 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91008 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91072 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 22366310 d288 d289
private def d283 : MobiusHarmonicTree := .branch 40344108 d284 d287
private def d275 : MobiusHarmonicTree := .branch 77582843 d276 d283
private def d259 : MobiusHarmonicTree := .branch 107523459 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91136 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91200 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 18968778 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91264 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91328 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 17213616 d297 d298
private def d292 : MobiusHarmonicTree := .branch 36182394 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91392 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91456 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 4548729 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91520 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91584 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 4770737 d304 d305
private def d299 : MobiusHarmonicTree := .branch 9319466 d300 d303
private def d291 : MobiusHarmonicTree := .branch 45501860 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91648 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91712 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 2769431 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91776 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91840 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 8982198 d312 d313
private def d307 : MobiusHarmonicTree := .branch 11751629 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91904 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 91968 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 10763473 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92032 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92096 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 11738914 d319 d320
private def d314 : MobiusHarmonicTree := .branch 22502387 d315 d318
private def d306 : MobiusHarmonicTree := .branch 34254016 d307 d314
private def d290 : MobiusHarmonicTree := .branch 79755876 d291 d306
private def d258 : MobiusHarmonicTree := .branch 187279335 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92160 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92224 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 15697732 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92288 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92352 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 22553581 d329 d330
private def d324 : MobiusHarmonicTree := .branch 38251313 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92416 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92480 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 37023827 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92544 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92608 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 32384410 d336 d337
private def d331 : MobiusHarmonicTree := .branch 69408237 d332 d335
private def d323 : MobiusHarmonicTree := .branch 107659550 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92672 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92736 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 39259423 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92800 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92864 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 60981256 d344 d345
private def d339 : MobiusHarmonicTree := .branch 100240679 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92928 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 92992 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 58833986 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93056 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93120 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 64109494 d351 d352
private def d346 : MobiusHarmonicTree := .branch 122943480 d347 d350
private def d338 : MobiusHarmonicTree := .branch 223184159 d339 d346
private def d322 : MobiusHarmonicTree := .branch 330843709 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93184 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93248 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 79013957 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93312 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93376 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 85033497 d360 d361
private def d355 : MobiusHarmonicTree := .branch 164047454 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93440 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93504 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 82499023 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93568 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93632 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 81245701 d367 d368
private def d362 : MobiusHarmonicTree := .branch 163744724 d363 d366
private def d354 : MobiusHarmonicTree := .branch 327792178 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93696 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93760 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 70788631 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93824 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93888 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 67888406 d375 d376
private def d370 : MobiusHarmonicTree := .branch 138677037 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 93952 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94016 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 84579647 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94080 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94144 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 98965346 d382 d383
private def d377 : MobiusHarmonicTree := .branch 183544993 d378 d381
private def d369 : MobiusHarmonicTree := .branch 322222030 d370 d377
private def d353 : MobiusHarmonicTree := .branch 650014208 d354 d369
private def d321 : MobiusHarmonicTree := .branch 980857917 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1168137252 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94208 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94272 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 93475487 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94336 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94400 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 109477674 d393 d394
private def d388 : MobiusHarmonicTree := .branch 202953161 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94464 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94528 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 128427900 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94592 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94656 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 126437760 d400 d401
private def d395 : MobiusHarmonicTree := .branch 254865660 d396 d399
private def d387 : MobiusHarmonicTree := .branch 457818821 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94720 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94784 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 123311458 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94848 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94912 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 134124119 d408 d409
private def d403 : MobiusHarmonicTree := .branch 257435577 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 94976 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95040 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 137722380 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95104 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95168 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 143442191 d415 d416
private def d410 : MobiusHarmonicTree := .branch 281164571 d411 d414
private def d402 : MobiusHarmonicTree := .branch 538600148 d403 d410
private def d386 : MobiusHarmonicTree := .branch 996418969 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95232 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95296 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 149787441 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95360 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95424 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 147415310 d424 d425
private def d419 : MobiusHarmonicTree := .branch 297202751 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95488 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95552 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 161996701 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95616 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95680 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 150901744 d431 d432
private def d426 : MobiusHarmonicTree := .branch 312898445 d427 d430
private def d418 : MobiusHarmonicTree := .branch 610101196 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95744 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95808 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 156029125 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95872 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 95936 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 166600707 d439 d440
private def d434 : MobiusHarmonicTree := .branch 322629832 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96000 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96064 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 161927627 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96128 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96192 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 151372868 d446 d447
private def d441 : MobiusHarmonicTree := .branch 313300495 d442 d445
private def d433 : MobiusHarmonicTree := .branch 635930327 d434 d441
private def d417 : MobiusHarmonicTree := .branch 1246031523 d418 d433
private def d385 : MobiusHarmonicTree := .branch 2242450492 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96256 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96320 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 161087857 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96384 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96448 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 160386744 d456 d457
private def d451 : MobiusHarmonicTree := .branch 321474601 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96512 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96576 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 158199443 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96640 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96704 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 143850514 d463 d464
private def d458 : MobiusHarmonicTree := .branch 302049957 d459 d462
private def d450 : MobiusHarmonicTree := .branch 623524558 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96768 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96832 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 163623041 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96896 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 96960 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 159687014 d471 d472
private def d466 : MobiusHarmonicTree := .branch 323310055 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97024 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97088 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 141226434 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97152 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97216 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 128993148 d478 d479
private def d473 : MobiusHarmonicTree := .branch 270219582 d474 d477
private def d465 : MobiusHarmonicTree := .branch 593529637 d466 d473
private def d449 : MobiusHarmonicTree := .branch 1217054195 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97280 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97344 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 114102449 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97408 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97472 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 116158476 d487 d488
private def d482 : MobiusHarmonicTree := .branch 230260925 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97536 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97600 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 101352819 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97664 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97728 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 91675787 d494 d495
private def d489 : MobiusHarmonicTree := .branch 193028606 d490 d493
private def d481 : MobiusHarmonicTree := .branch 423289531 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97792 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97856 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 89590803 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97920 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 97984 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 93710191 d502 d503
private def d497 : MobiusHarmonicTree := .branch 183300994 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98048 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98112 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 87177287 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98176 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock011 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98240 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 96355749 d509 d510
private def d504 : MobiusHarmonicTree := .branch 183533036 d505 d508
private def d496 : MobiusHarmonicTree := .branch 366834030 d497 d504
private def d480 : MobiusHarmonicTree := .branch 790123561 d481 d496
private def d448 : MobiusHarmonicTree := .branch 2007177756 d449 d480
private def d384 : MobiusHarmonicTree := .branch 4249628248 d385 d448
private def d256 : MobiusHarmonicTree := .branch 5417765500 d257 d384
private def d0 : MobiusHarmonicTree := .branch 8359185758 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 81920 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 81920 8359185758 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 81920 2941420258 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 81920 1467364182 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 81920 961759524 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 81920 600096653 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 81920 266611954 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 81920 98844540 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 81920 43518159 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 82048 55326381 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 82176 167767414 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 82176 76251859 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 82304 91515555 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 82432 333484699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 82432 171209252 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 82432 84041436 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 82560 87167816 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 82688 162275447 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 82688 80433849 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 82816 81841598 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 82944 361662871 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 82944 248613745 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 82944 147151290 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 82944 80740167 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 83072 66411123 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 83200 101462455 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 83200 55079130 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 83328 46383325 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 83456 113049126 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 83456 76451165 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 83456 37011909 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 83584 39439256 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 83712 36597961 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 83712 27361988 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 83840 9235973 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 83968 505604658 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 83968 94813731 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 83968 25545213 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 83968 13864941 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 83968 6796433 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 84096 7068508 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 84224 11680272 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 84224 7937351 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 84352 3742921 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 84480 69268518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 84480 14623783 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 84480 9700277 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 84608 4923506 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 84736 54644735 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 84736 17580040 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 84864 37064695 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 84992 410790927 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 84992 141293977 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 84992 70344670 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 84992 32732948 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 85120 37611722 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 85248 70949307 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 85248 31530771 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 85376 39418536 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 85504 269496950 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 85504 107545832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 85504 49737918 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 85632 57807914 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 85760 161951118 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 85760 72459968 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 85888 89491150 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 86016 1474056076 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 86016 862326406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 86016 496577763 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 86016 282256289 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 86016 168951585 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 86016 90731074 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 86144 78220511 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 86272 113304704 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 86272 65016455 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 86400 48288249 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 86528 214321474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 86528 106746258 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 86528 47346510 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 86656 59399748 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 86784 107575216 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 86784 55892249 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 86912 51682967 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 87040 365748643 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 87040 202582013 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 87040 107111751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 87040 50364483 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 87168 56747268 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 87296 95470262 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 87296 43418692 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 87424 52051570 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 87552 163166630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 87552 96266739 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 87552 58404176 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 87680 37862563 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 87808 66899891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 87808 31989506 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 87936 34910385 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 88064 611729670 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 88064 451513497 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 88064 235767217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 88064 106345489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 88064 45533113 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 88192 60812376 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 88320 129421728 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 88320 64502752 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 88448 64918976 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 88576 215746280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 88576 127997506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 88576 60968812 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 88704 67028694 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 88832 87748774 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 88832 49768872 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 88960 37979902 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 89088 160216173 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 89088 114214988 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 89088 63190467 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 89088 28882200 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 89216 34308267 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 89344 51024521 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 89344 33252882 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 89472 17771639 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 89600 46001185 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 89600 17890465 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 89600 10629911 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 89728 7260554 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 89856 28110720 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 89856 18281601 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 89984 9829119 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 90112 5417765500 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 90112 1168137252 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 90112 187279335 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 90112 107523459 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 90112 29940616 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 90112 21223390 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 90112 11964161 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 90240 9259229 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 90368 8717226 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 90368 3771532 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 90496 4945694 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 90624 77582843 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 90624 37238735 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 90624 14741401 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 90752 22497334 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 90880 40344108 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 90880 17977798 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 91008 22366310 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 91136 79755876 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 91136 45501860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 91136 36182394 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 91136 18968778 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 91264 17213616 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 91392 9319466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 91392 4548729 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 91520 4770737 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 91648 34254016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 91648 11751629 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 91648 2769431 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 91776 8982198 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 91904 22502387 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 91904 10763473 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 92032 11738914 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 92160 980857917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 92160 330843709 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 92160 107659550 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 92160 38251313 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 92160 15697732 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 92288 22553581 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 92416 69408237 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 92416 37023827 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 92544 32384410 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 92672 223184159 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 92672 100240679 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 92672 39259423 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 92800 60981256 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 92928 122943480 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 92928 58833986 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 93056 64109494 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 93184 650014208 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 93184 327792178 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 93184 164047454 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 93184 79013957 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 93312 85033497 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 93440 163744724 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 93440 82499023 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 93568 81245701 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 93696 322222030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 93696 138677037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 93696 70788631 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 93824 67888406 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 93952 183544993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 93952 84579647 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 94080 98965346 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 94208 4249628248 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 94208 2242450492 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 94208 996418969 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 94208 457818821 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 94208 202953161 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 94208 93475487 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 94336 109477674 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 94464 254865660 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 94464 128427900 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 94592 126437760 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 94720 538600148 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 94720 257435577 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 94720 123311458 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 94848 134124119 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 94976 281164571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 94976 137722380 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 95104 143442191 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 95232 1246031523 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 95232 610101196 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 95232 297202751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 95232 149787441 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 95360 147415310 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 95488 312898445 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 95488 161996701 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 95616 150901744 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 95744 635930327 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 95744 322629832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 95744 156029125 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 95872 166600707 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 96000 313300495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 96000 161927627 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 96128 151372868 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 96256 2007177756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 96256 1217054195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 96256 623524558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 96256 321474601 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 96256 161087857 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 96384 160386744 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 96512 302049957 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 96512 158199443 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 96640 143850514 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 96768 593529637 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 96768 323310055 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 96768 163623041 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 96896 159687014 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 97024 270219582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 97024 141226434 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 97152 128993148 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 97280 790123561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 97280 423289531 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 97280 230260925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 97280 114102449 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 97408 116158476 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 97536 193028606 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 97536 101352819 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 97664 91675787 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 97792 366834030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 97792 183300994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 97792 89590803 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 97920 93710191 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 98048 183533036 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 98048 87177287 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 98176 96355749 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 81920 (MobiusHarmonicTree.branch 8359185758 mobiusHarmonicBlock010 mobiusHarmonicBlock011) = true := Helfgott.combined

#print axioms solution
