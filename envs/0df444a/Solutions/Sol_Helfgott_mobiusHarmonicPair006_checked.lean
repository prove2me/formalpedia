-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair006_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:11:46.39276+00:00
-- url     : https://prove2.me/submissions/41a9bcec-a500-4e55-9b6c-3415f92d958f

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98304 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98368 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 88293711 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98432 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98496 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 81658314 d11 d12
private def d6 : MobiusHarmonicTree := .branch 169952025 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98560 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98624 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 80447492 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98688 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98752 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 82116314 d18 d19
private def d13 : MobiusHarmonicTree := .branch 162563806 d14 d17
private def d5 : MobiusHarmonicTree := .branch 332515831 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98816 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98880 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 79003119 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 98944 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99008 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 83761457 d26 d27
private def d21 : MobiusHarmonicTree := .branch 162764576 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99072 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99136 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 80634821 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99200 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99264 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 88583279 d33 d34
private def d28 : MobiusHarmonicTree := .branch 169218100 d29 d32
private def d20 : MobiusHarmonicTree := .branch 331982676 d21 d28
private def d4 : MobiusHarmonicTree := .branch 664498507 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99328 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99392 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 78608038 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99456 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99520 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 73763666 d42 d43
private def d37 : MobiusHarmonicTree := .branch 152371704 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99584 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99648 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 69094041 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99712 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99776 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 73564259 d49 d50
private def d44 : MobiusHarmonicTree := .branch 142658300 d45 d48
private def d36 : MobiusHarmonicTree := .branch 295030004 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99840 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99904 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 75914410 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 99968 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100032 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 54585408 d57 d58
private def d52 : MobiusHarmonicTree := .branch 130499818 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100096 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100160 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 45647670 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100224 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100288 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 36148056 d64 d65
private def d59 : MobiusHarmonicTree := .branch 81795726 d60 d63
private def d51 : MobiusHarmonicTree := .branch 212295544 d52 d59
private def d35 : MobiusHarmonicTree := .branch 507325548 d36 d51
private def d3 : MobiusHarmonicTree := .branch 1171824055 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100352 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100416 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 27257003 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100480 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100544 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 37148406 d74 d75
private def d69 : MobiusHarmonicTree := .branch 64405409 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100608 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100672 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 29234079 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100736 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100800 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 11867195 d81 d82
private def d76 : MobiusHarmonicTree := .branch 41101274 d77 d80
private def d68 : MobiusHarmonicTree := .branch 105506683 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100864 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100928 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 4576540 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 100992 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101056 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 17881694 d89 d90
private def d84 : MobiusHarmonicTree := .branch 22458234 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101120 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101184 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 22375231 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101248 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101312 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 14745139 d96 d97
private def d91 : MobiusHarmonicTree := .branch 37120370 d92 d95
private def d83 : MobiusHarmonicTree := .branch 59578604 d84 d91
private def d67 : MobiusHarmonicTree := .branch 165085287 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101376 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101440 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 26093354 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101504 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101568 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 42915444 d105 d106
private def d100 : MobiusHarmonicTree := .branch 69008798 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101632 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101696 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 49953156 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101760 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101824 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 44999893 d112 d113
private def d107 : MobiusHarmonicTree := .branch 94953049 d108 d111
private def d99 : MobiusHarmonicTree := .branch 163961847 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101888 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 101952 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 45639901 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102016 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102080 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 59961389 d120 d121
private def d115 : MobiusHarmonicTree := .branch 105601290 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102144 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102208 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 75677998 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102272 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102336 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 84232608 d127 d128
private def d122 : MobiusHarmonicTree := .branch 159910606 d123 d126
private def d114 : MobiusHarmonicTree := .branch 265511896 d115 d122
private def d98 : MobiusHarmonicTree := .branch 429473743 d99 d114
private def d66 : MobiusHarmonicTree := .branch 594559030 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1766383085 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102400 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102464 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 70406448 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102528 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102592 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 71213144 d138 d139
private def d133 : MobiusHarmonicTree := .branch 141619592 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102656 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102720 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 69988455 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102784 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102848 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 66262501 d145 d146
private def d140 : MobiusHarmonicTree := .branch 136250956 d141 d144
private def d132 : MobiusHarmonicTree := .branch 277870548 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102912 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 102976 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 59685491 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103040 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103104 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 48331073 d153 d154
private def d148 : MobiusHarmonicTree := .branch 108016564 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103168 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103232 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 42836451 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103296 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103360 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 31880698 d160 d161
private def d155 : MobiusHarmonicTree := .branch 74717149 d156 d159
private def d147 : MobiusHarmonicTree := .branch 182733713 d148 d155
private def d131 : MobiusHarmonicTree := .branch 460604261 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103424 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103488 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 16351187 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103552 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103616 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 6235495 d169 d170
private def d164 : MobiusHarmonicTree := .branch 22586682 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103680 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103744 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 8876305 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103808 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103872 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 18090067 d176 d177
private def d171 : MobiusHarmonicTree := .branch 26966372 d172 d175
private def d163 : MobiusHarmonicTree := .branch 49553054 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 103936 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104000 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 12089162 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104064 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104128 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 3918680 d184 d185
private def d179 : MobiusHarmonicTree := .branch 16007842 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104192 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104256 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 6704052 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104320 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104384 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 2050190 d191 d192
private def d186 : MobiusHarmonicTree := .branch 8754242 d187 d190
private def d178 : MobiusHarmonicTree := .branch 24762084 d179 d186
private def d162 : MobiusHarmonicTree := .branch 74315138 d163 d178
private def d130 : MobiusHarmonicTree := .branch 534919399 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104448 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104512 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 3099829 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104576 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104640 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 4080686 d201 d202
private def d196 : MobiusHarmonicTree := .branch 7180515 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104704 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104768 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 15299028 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104832 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104896 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 24528643 d208 d209
private def d203 : MobiusHarmonicTree := .branch 39827671 d204 d207
private def d195 : MobiusHarmonicTree := .branch 47008186 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 104960 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105024 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 34705717 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105088 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105152 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 26306429 d216 d217
private def d211 : MobiusHarmonicTree := .branch 61012146 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105216 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105280 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 33252782 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105344 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105408 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 38375964 d223 d224
private def d218 : MobiusHarmonicTree := .branch 71628746 d219 d222
private def d210 : MobiusHarmonicTree := .branch 132640892 d211 d218
private def d194 : MobiusHarmonicTree := .branch 179649078 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105472 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105536 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 31722911 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105600 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105664 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 35195339 d232 d233
private def d227 : MobiusHarmonicTree := .branch 66918250 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105728 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105792 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 38179770 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105856 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105920 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 30647058 d239 d240
private def d234 : MobiusHarmonicTree := .branch 68826828 d235 d238
private def d226 : MobiusHarmonicTree := .branch 135745078 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 105984 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106048 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 23904368 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106112 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106176 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 26635738 d247 d248
private def d242 : MobiusHarmonicTree := .branch 50540106 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106240 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106304 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 30064118 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106368 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock012 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106432 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 38314851 d254 d255
private def d249 : MobiusHarmonicTree := .branch 68378969 d250 d253
private def d241 : MobiusHarmonicTree := .branch 118919075 d242 d249
private def d225 : MobiusHarmonicTree := .branch 254664153 d226 d241
private def d193 : MobiusHarmonicTree := .branch 434313231 d194 d225
private def d129 : MobiusHarmonicTree := .branch 969232630 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2735615715 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106496 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106560 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 31185667 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106624 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106688 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 28615372 d266 d267
private def d261 : MobiusHarmonicTree := .branch 59801039 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106752 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106816 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 34837390 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106880 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 106944 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 25554688 d273 d274
private def d268 : MobiusHarmonicTree := .branch 60392078 d269 d272
private def d260 : MobiusHarmonicTree := .branch 120193117 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107008 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107072 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 31248595 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107136 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107200 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 25813293 d281 d282
private def d276 : MobiusHarmonicTree := .branch 57061888 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107264 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107328 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 18531048 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107392 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107456 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 16175297 d288 d289
private def d283 : MobiusHarmonicTree := .branch 34706345 d284 d287
private def d275 : MobiusHarmonicTree := .branch 91768233 d276 d283
private def d259 : MobiusHarmonicTree := .branch 211961350 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107520 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107584 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 4740855 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107648 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107712 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 4456353 d297 d298
private def d292 : MobiusHarmonicTree := .branch 9197208 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107776 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107840 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 3885799 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107904 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 107968 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 6500729 d304 d305
private def d299 : MobiusHarmonicTree := .branch 10386528 d300 d303
private def d291 : MobiusHarmonicTree := .branch 19583736 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108032 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108096 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 18982962 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108160 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108224 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 19939988 d312 d313
private def d307 : MobiusHarmonicTree := .branch 38922950 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108288 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108352 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 11592655 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108416 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108480 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 4987540 d319 d320
private def d314 : MobiusHarmonicTree := .branch 16580195 d315 d318
private def d306 : MobiusHarmonicTree := .branch 55503145 d307 d314
private def d290 : MobiusHarmonicTree := .branch 75086881 d291 d306
private def d258 : MobiusHarmonicTree := .branch 287048231 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108544 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108608 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 4724357 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108672 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108736 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 6390789 d329 d330
private def d324 : MobiusHarmonicTree := .branch 11115146 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108800 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108864 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 6743314 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108928 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 108992 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 4054496 d336 d337
private def d331 : MobiusHarmonicTree := .branch 10797810 d332 d335
private def d323 : MobiusHarmonicTree := .branch 21912956 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109056 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109120 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 7597606 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109184 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109248 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 7523863 d344 d345
private def d339 : MobiusHarmonicTree := .branch 15121469 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109312 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109376 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 4187954 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109440 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109504 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 5542869 d351 d352
private def d346 : MobiusHarmonicTree := .branch 9730823 d347 d350
private def d338 : MobiusHarmonicTree := .branch 24852292 d339 d346
private def d322 : MobiusHarmonicTree := .branch 46765248 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109568 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109632 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 8492755 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109696 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109760 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 4182083 d360 d361
private def d355 : MobiusHarmonicTree := .branch 12674838 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109824 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109888 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 11073564 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 109952 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110016 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 15161197 d367 d368
private def d362 : MobiusHarmonicTree := .branch 26234761 d363 d366
private def d354 : MobiusHarmonicTree := .branch 38909599 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110080 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110144 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 9061705 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110208 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110272 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 10992093 d375 d376
private def d370 : MobiusHarmonicTree := .branch 20053798 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110336 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110400 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 14337133 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110464 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110528 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 15589881 d382 d383
private def d377 : MobiusHarmonicTree := .branch 29927014 d378 d381
private def d369 : MobiusHarmonicTree := .branch 49980812 d370 d377
private def d353 : MobiusHarmonicTree := .branch 88890411 d354 d369
private def d321 : MobiusHarmonicTree := .branch 135655659 d322 d353
private def d257 : MobiusHarmonicTree := .branch 422703890 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110592 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110656 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 5809713 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110720 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110784 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 20327027 d393 d394
private def d388 : MobiusHarmonicTree := .branch 26136740 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110848 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110912 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 10235767 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 110976 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111040 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 5024735 d400 d401
private def d395 : MobiusHarmonicTree := .branch 15260502 d396 d399
private def d387 : MobiusHarmonicTree := .branch 41397242 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111104 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111168 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 2959727 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111232 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111296 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 2255384 d408 d409
private def d403 : MobiusHarmonicTree := .branch 5215111 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111360 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111424 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 15129410 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111488 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111552 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 15579340 d415 d416
private def d410 : MobiusHarmonicTree := .branch 30708750 d411 d414
private def d402 : MobiusHarmonicTree := .branch 35923861 d403 d410
private def d386 : MobiusHarmonicTree := .branch 77321103 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111616 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111680 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 21130979 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111744 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111808 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 33807009 d424 d425
private def d419 : MobiusHarmonicTree := .branch 54937988 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111872 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 111936 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 42666961 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112000 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112064 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 50328936 d431 d432
private def d426 : MobiusHarmonicTree := .branch 92995897 d427 d430
private def d418 : MobiusHarmonicTree := .branch 147933885 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112128 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112192 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 44307777 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112256 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112320 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 38169315 d439 d440
private def d434 : MobiusHarmonicTree := .branch 82477092 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112384 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112448 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 41672141 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112512 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112576 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 43900870 d446 d447
private def d441 : MobiusHarmonicTree := .branch 85573011 d442 d445
private def d433 : MobiusHarmonicTree := .branch 168050103 d434 d441
private def d417 : MobiusHarmonicTree := .branch 315983988 d418 d433
private def d385 : MobiusHarmonicTree := .branch 393305091 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112640 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112704 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 49463830 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112768 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112832 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 63039624 d456 d457
private def d451 : MobiusHarmonicTree := .branch 112503454 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112896 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 112960 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 70829372 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113024 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113088 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 68071176 d463 d464
private def d458 : MobiusHarmonicTree := .branch 138900548 d459 d462
private def d450 : MobiusHarmonicTree := .branch 251404002 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113152 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113216 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 57695827 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113280 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113344 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 57991801 d471 d472
private def d466 : MobiusHarmonicTree := .branch 115687628 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113408 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113472 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 61186992 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113536 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113600 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 74320177 d478 d479
private def d473 : MobiusHarmonicTree := .branch 135507169 d474 d477
private def d465 : MobiusHarmonicTree := .branch 251194797 d466 d473
private def d449 : MobiusHarmonicTree := .branch 502598799 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113664 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113728 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 81678351 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113792 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113856 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 84728457 d487 d488
private def d482 : MobiusHarmonicTree := .branch 166406808 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113920 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 113984 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 98645872 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114048 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114112 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 94328875 d494 d495
private def d489 : MobiusHarmonicTree := .branch 192974747 d490 d493
private def d481 : MobiusHarmonicTree := .branch 359381555 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114176 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114240 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 95036109 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114304 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114368 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 94991860 d502 d503
private def d497 : MobiusHarmonicTree := .branch 190027969 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114432 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114496 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 92405201 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114560 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock013 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 114624 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 100703985 d509 d510
private def d504 : MobiusHarmonicTree := .branch 193109186 d505 d508
private def d496 : MobiusHarmonicTree := .branch 383137155 d497 d504
private def d480 : MobiusHarmonicTree := .branch 742518710 d481 d496
private def d448 : MobiusHarmonicTree := .branch 1245117509 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1638422600 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2061126490 d257 d384
private def d0 : MobiusHarmonicTree := .branch 4796742205 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 98304 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 98304 4796742205 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 98304 2735615715 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 98304 1766383085 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 98304 1171824055 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 98304 664498507 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 98304 332515831 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 98304 169952025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 98304 88293711 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 98432 81658314 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 98560 162563806 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 98560 80447492 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 98688 82116314 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 98816 331982676 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 98816 162764576 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 98816 79003119 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 98944 83761457 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 99072 169218100 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 99072 80634821 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 99200 88583279 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 99328 507325548 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 99328 295030004 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 99328 152371704 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 99328 78608038 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 99456 73763666 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 99584 142658300 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 99584 69094041 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 99712 73564259 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 99840 212295544 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 99840 130499818 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 99840 75914410 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 99968 54585408 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 100096 81795726 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 100096 45647670 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 100224 36148056 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 100352 594559030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 100352 165085287 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 100352 105506683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 100352 64405409 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 100352 27257003 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 100480 37148406 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 100608 41101274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 100608 29234079 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 100736 11867195 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 100864 59578604 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 100864 22458234 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 100864 4576540 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 100992 17881694 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 101120 37120370 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 101120 22375231 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 101248 14745139 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 101376 429473743 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 101376 163961847 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 101376 69008798 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 101376 26093354 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 101504 42915444 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 101632 94953049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 101632 49953156 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 101760 44999893 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 101888 265511896 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 101888 105601290 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 101888 45639901 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 102016 59961389 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 102144 159910606 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 102144 75677998 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 102272 84232608 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 102400 969232630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 102400 534919399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 102400 460604261 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 102400 277870548 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 102400 141619592 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 102400 70406448 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 102528 71213144 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 102656 136250956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 102656 69988455 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 102784 66262501 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 102912 182733713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 102912 108016564 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 102912 59685491 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 103040 48331073 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 103168 74717149 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 103168 42836451 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 103296 31880698 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 103424 74315138 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 103424 49553054 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 103424 22586682 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 103424 16351187 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 103552 6235495 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 103680 26966372 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 103680 8876305 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 103808 18090067 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 103936 24762084 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 103936 16007842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 103936 12089162 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 104064 3918680 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 104192 8754242 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 104192 6704052 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 104320 2050190 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 104448 434313231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 104448 179649078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 104448 47008186 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 104448 7180515 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 104448 3099829 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 104576 4080686 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 104704 39827671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 104704 15299028 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 104832 24528643 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 104960 132640892 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 104960 61012146 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 104960 34705717 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 105088 26306429 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 105216 71628746 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 105216 33252782 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 105344 38375964 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 105472 254664153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 105472 135745078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 105472 66918250 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 105472 31722911 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 105600 35195339 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 105728 68826828 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 105728 38179770 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 105856 30647058 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 105984 118919075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 105984 50540106 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 105984 23904368 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 106112 26635738 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 106240 68378969 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 106240 30064118 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 106368 38314851 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 106496 2061126490 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 106496 422703890 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 106496 287048231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 106496 211961350 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 106496 120193117 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 106496 59801039 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 106496 31185667 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 106624 28615372 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 106752 60392078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 106752 34837390 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 106880 25554688 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 107008 91768233 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 107008 57061888 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 107008 31248595 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 107136 25813293 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 107264 34706345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 107264 18531048 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 107392 16175297 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 107520 75086881 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 107520 19583736 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 107520 9197208 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 107520 4740855 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 107648 4456353 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 107776 10386528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 107776 3885799 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 107904 6500729 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 108032 55503145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 108032 38922950 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 108032 18982962 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 108160 19939988 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 108288 16580195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 108288 11592655 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 108416 4987540 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 108544 135655659 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 108544 46765248 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 108544 21912956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 108544 11115146 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 108544 4724357 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 108672 6390789 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 108800 10797810 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 108800 6743314 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 108928 4054496 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 109056 24852292 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 109056 15121469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 109056 7597606 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 109184 7523863 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 109312 9730823 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 109312 4187954 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 109440 5542869 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 109568 88890411 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 109568 38909599 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 109568 12674838 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 109568 8492755 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 109696 4182083 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 109824 26234761 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 109824 11073564 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 109952 15161197 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 110080 49980812 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 110080 20053798 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 110080 9061705 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 110208 10992093 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 110336 29927014 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 110336 14337133 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 110464 15589881 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 110592 1638422600 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 110592 393305091 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 110592 77321103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 110592 41397242 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 110592 26136740 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 110592 5809713 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 110720 20327027 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 110848 15260502 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 110848 10235767 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 110976 5024735 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 111104 35923861 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 111104 5215111 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 111104 2959727 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 111232 2255384 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 111360 30708750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 111360 15129410 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 111488 15579340 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 111616 315983988 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 111616 147933885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 111616 54937988 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 111616 21130979 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 111744 33807009 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 111872 92995897 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 111872 42666961 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 112000 50328936 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 112128 168050103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 112128 82477092 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 112128 44307777 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 112256 38169315 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 112384 85573011 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 112384 41672141 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 112512 43900870 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 112640 1245117509 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 112640 502598799 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 112640 251404002 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 112640 112503454 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 112640 49463830 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 112768 63039624 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 112896 138900548 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 112896 70829372 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 113024 68071176 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 113152 251194797 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 113152 115687628 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 113152 57695827 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 113280 57991801 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 113408 135507169 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 113408 61186992 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 113536 74320177 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 113664 742518710 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 113664 359381555 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 113664 166406808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 113664 81678351 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 113792 84728457 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 113920 192974747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 113920 98645872 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 114048 94328875 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 114176 383137155 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 114176 190027969 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 114176 95036109 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 114304 94991860 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 114432 193109186 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 114432 92405201 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 114560 100703985 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 98304 (MobiusHarmonicTree.branch 4796742205 mobiusHarmonicBlock012 mobiusHarmonicBlock013) = true := Helfgott.combined

#print axioms solution
