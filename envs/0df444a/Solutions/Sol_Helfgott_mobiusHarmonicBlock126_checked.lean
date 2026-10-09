-- Prove2me | solution 1 for Helfgott.mobiusHarmonicBlock126_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:09:45.277594+00:00
-- url     : https://prove2.me/submissions/051d12cd-2336-4275-8cdc-b64e66b0c3f3

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

private abbrev d7 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 0
private theorem p7 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032192 d7 = true := by decide +kernel

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 1
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032256 d8 = true := by decide +kernel

private def d6 : MobiusHarmonicTree := .branch 11677427 d7 d8
private abbrev d10 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 2
private theorem p10 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032320 d10 = true := by decide +kernel

private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 3
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032384 d11 = true := by decide +kernel

private def d9 : MobiusHarmonicTree := .branch 11471554 d10 d11
private def d5 : MobiusHarmonicTree := .branch 23148981 d6 d9
private abbrev d14 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 4
private theorem p14 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032448 d14 = true := by decide +kernel

private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 5
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032512 d15 = true := by decide +kernel

private def d13 : MobiusHarmonicTree := .branch 13234761 d14 d15
private abbrev d17 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 6
private theorem p17 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032576 d17 = true := by decide +kernel

private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 7
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032640 d18 = true := by decide +kernel

private def d16 : MobiusHarmonicTree := .branch 14369062 d17 d18
private def d12 : MobiusHarmonicTree := .branch 27603823 d13 d16
private def d4 : MobiusHarmonicTree := .branch 50752804 d5 d12
private abbrev d22 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 8
private theorem p22 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032704 d22 = true := by decide +kernel

private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 9
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032768 d23 = true := by decide +kernel

private def d21 : MobiusHarmonicTree := .branch 14032259 d22 d23
private abbrev d25 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 10
private theorem p25 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032832 d25 = true := by decide +kernel

private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 11
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032896 d26 = true := by decide +kernel

private def d24 : MobiusHarmonicTree := .branch 15564056 d25 d26
private def d20 : MobiusHarmonicTree := .branch 29596315 d21 d24
private abbrev d29 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 12
private theorem p29 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1032960 d29 = true := by decide +kernel

private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 13
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033024 d30 = true := by decide +kernel

private def d28 : MobiusHarmonicTree := .branch 16797351 d29 d30
private abbrev d32 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 14
private theorem p32 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033088 d32 = true := by decide +kernel

private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 15
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033152 d33 = true := by decide +kernel

private def d31 : MobiusHarmonicTree := .branch 17684776 d32 d33
private def d27 : MobiusHarmonicTree := .branch 34482127 d28 d31
private def d19 : MobiusHarmonicTree := .branch 64078442 d20 d27
private def d3 : MobiusHarmonicTree := .branch 114831246 d4 d19
private abbrev d38 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 16
private theorem p38 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033216 d38 = true := by decide +kernel

private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 17
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033280 d39 = true := by decide +kernel

private def d37 : MobiusHarmonicTree := .branch 18712326 d38 d39
private abbrev d41 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 18
private theorem p41 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033344 d41 = true := by decide +kernel

private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 19
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033408 d42 = true := by decide +kernel

private def d40 : MobiusHarmonicTree := .branch 17799433 d41 d42
private def d36 : MobiusHarmonicTree := .branch 36511759 d37 d40
private abbrev d45 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 20
private theorem p45 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033472 d45 = true := by decide +kernel

private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 21
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033536 d46 = true := by decide +kernel

private def d44 : MobiusHarmonicTree := .branch 16880978 d45 d46
private abbrev d48 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 22
private theorem p48 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033600 d48 = true := by decide +kernel

private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 23
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033664 d49 = true := by decide +kernel

private def d47 : MobiusHarmonicTree := .branch 16730835 d48 d49
private def d43 : MobiusHarmonicTree := .branch 33611813 d44 d47
private def d35 : MobiusHarmonicTree := .branch 70123572 d36 d43
private abbrev d53 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 24
private theorem p53 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033728 d53 = true := by decide +kernel

private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 25
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033792 d54 = true := by decide +kernel

private def d52 : MobiusHarmonicTree := .branch 17056709 d53 d54
private abbrev d56 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 26
private theorem p56 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033856 d56 = true := by decide +kernel

private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 27
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033920 d57 = true := by decide +kernel

private def d55 : MobiusHarmonicTree := .branch 17175477 d56 d57
private def d51 : MobiusHarmonicTree := .branch 34232186 d52 d55
private abbrev d60 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 28
private theorem p60 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1033984 d60 = true := by decide +kernel

private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 29
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034048 d61 = true := by decide +kernel

private def d59 : MobiusHarmonicTree := .branch 18385087 d60 d61
private abbrev d63 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 30
private theorem p63 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034112 d63 = true := by decide +kernel

private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 31
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034176 d64 = true := by decide +kernel

private def d62 : MobiusHarmonicTree := .branch 18258098 d63 d64
private def d58 : MobiusHarmonicTree := .branch 36643185 d59 d62
private def d50 : MobiusHarmonicTree := .branch 70875371 d51 d58
private def d34 : MobiusHarmonicTree := .branch 140998943 d35 d50
private def d2 : MobiusHarmonicTree := .branch 255830189 d3 d34
private abbrev d70 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 32
private theorem p70 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034240 d70 = true := by decide +kernel

private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 33
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034304 d71 = true := by decide +kernel

private def d69 : MobiusHarmonicTree := .branch 16942871 d70 d71
private abbrev d73 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 34
private theorem p73 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034368 d73 = true := by decide +kernel

private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 35
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034432 d74 = true := by decide +kernel

private def d72 : MobiusHarmonicTree := .branch 16458379 d73 d74
private def d68 : MobiusHarmonicTree := .branch 33401250 d69 d72
private abbrev d77 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 36
private theorem p77 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034496 d77 = true := by decide +kernel

private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 37
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034560 d78 = true := by decide +kernel

private def d76 : MobiusHarmonicTree := .branch 16903872 d77 d78
private abbrev d80 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 38
private theorem p80 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034624 d80 = true := by decide +kernel

private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 39
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034688 d81 = true := by decide +kernel

private def d79 : MobiusHarmonicTree := .branch 18731288 d80 d81
private def d75 : MobiusHarmonicTree := .branch 35635160 d76 d79
private def d67 : MobiusHarmonicTree := .branch 69036410 d68 d75
private abbrev d85 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 40
private theorem p85 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034752 d85 = true := by decide +kernel

private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 41
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034816 d86 = true := by decide +kernel

private def d84 : MobiusHarmonicTree := .branch 19882832 d85 d86
private abbrev d88 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 42
private theorem p88 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034880 d88 = true := by decide +kernel

private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 43
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1034944 d89 = true := by decide +kernel

private def d87 : MobiusHarmonicTree := .branch 20428224 d88 d89
private def d83 : MobiusHarmonicTree := .branch 40311056 d84 d87
private abbrev d92 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 44
private theorem p92 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035008 d92 = true := by decide +kernel

private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 45
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035072 d93 = true := by decide +kernel

private def d91 : MobiusHarmonicTree := .branch 20507816 d92 d93
private abbrev d95 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 46
private theorem p95 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035136 d95 = true := by decide +kernel

private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 47
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035200 d96 = true := by decide +kernel

private def d94 : MobiusHarmonicTree := .branch 21803567 d95 d96
private def d90 : MobiusHarmonicTree := .branch 42311383 d91 d94
private def d82 : MobiusHarmonicTree := .branch 82622439 d83 d90
private def d66 : MobiusHarmonicTree := .branch 151658849 d67 d82
private abbrev d101 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 48
private theorem p101 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035264 d101 = true := by decide +kernel

private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 49
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035328 d102 = true := by decide +kernel

private def d100 : MobiusHarmonicTree := .branch 22302197 d101 d102
private abbrev d104 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 50
private theorem p104 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035392 d104 = true := by decide +kernel

private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 51
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035456 d105 = true := by decide +kernel

private def d103 : MobiusHarmonicTree := .branch 22056064 d104 d105
private def d99 : MobiusHarmonicTree := .branch 44358261 d100 d103
private abbrev d108 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 52
private theorem p108 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035520 d108 = true := by decide +kernel

private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 53
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035584 d109 = true := by decide +kernel

private def d107 : MobiusHarmonicTree := .branch 20914854 d108 d109
private abbrev d111 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 54
private theorem p111 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035648 d111 = true := by decide +kernel

private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 55
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035712 d112 = true := by decide +kernel

private def d110 : MobiusHarmonicTree := .branch 21028099 d111 d112
private def d106 : MobiusHarmonicTree := .branch 41942953 d107 d110
private def d98 : MobiusHarmonicTree := .branch 86301214 d99 d106
private abbrev d116 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 56
private theorem p116 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035776 d116 = true := by decide +kernel

private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 57
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035840 d117 = true := by decide +kernel

private def d115 : MobiusHarmonicTree := .branch 22587519 d116 d117
private abbrev d119 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 58
private theorem p119 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035904 d119 = true := by decide +kernel

private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 59
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1035968 d120 = true := by decide +kernel

private def d118 : MobiusHarmonicTree := .branch 23251769 d119 d120
private def d114 : MobiusHarmonicTree := .branch 45839288 d115 d118
private abbrev d123 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 60
private theorem p123 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036032 d123 = true := by decide +kernel

private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 61
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036096 d124 = true := by decide +kernel

private def d122 : MobiusHarmonicTree := .branch 20990442 d123 d124
private abbrev d126 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 62
private theorem p126 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036160 d126 = true := by decide +kernel

private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 63
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036224 d127 = true := by decide +kernel

private def d125 : MobiusHarmonicTree := .branch 20826654 d126 d127
private def d121 : MobiusHarmonicTree := .branch 41817096 d122 d125
private def d113 : MobiusHarmonicTree := .branch 87656384 d114 d121
private def d97 : MobiusHarmonicTree := .branch 173957598 d98 d113
private def d65 : MobiusHarmonicTree := .branch 325616447 d66 d97
private def d1 : MobiusHarmonicTree := .branch 581446636 d2 d65
private abbrev d134 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 64
private theorem p134 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036288 d134 = true := by decide +kernel

private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 65
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036352 d135 = true := by decide +kernel

private def d133 : MobiusHarmonicTree := .branch 21033462 d134 d135
private abbrev d137 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 66
private theorem p137 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036416 d137 = true := by decide +kernel

private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 67
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036480 d138 = true := by decide +kernel

private def d136 : MobiusHarmonicTree := .branch 21874112 d137 d138
private def d132 : MobiusHarmonicTree := .branch 42907574 d133 d136
private abbrev d141 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 68
private theorem p141 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036544 d141 = true := by decide +kernel

private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 69
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036608 d142 = true := by decide +kernel

private def d140 : MobiusHarmonicTree := .branch 22275598 d141 d142
private abbrev d144 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 70
private theorem p144 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036672 d144 = true := by decide +kernel

private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 71
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036736 d145 = true := by decide +kernel

private def d143 : MobiusHarmonicTree := .branch 22553555 d144 d145
private def d139 : MobiusHarmonicTree := .branch 44829153 d140 d143
private def d131 : MobiusHarmonicTree := .branch 87736727 d132 d139
private abbrev d149 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 72
private theorem p149 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036800 d149 = true := by decide +kernel

private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 73
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036864 d150 = true := by decide +kernel

private def d148 : MobiusHarmonicTree := .branch 21792713 d149 d150
private abbrev d152 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 74
private theorem p152 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036928 d152 = true := by decide +kernel

private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 75
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1036992 d153 = true := by decide +kernel

private def d151 : MobiusHarmonicTree := .branch 22081248 d152 d153
private def d147 : MobiusHarmonicTree := .branch 43873961 d148 d151
private abbrev d156 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 76
private theorem p156 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037056 d156 = true := by decide +kernel

private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 77
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037120 d157 = true := by decide +kernel

private def d155 : MobiusHarmonicTree := .branch 21738165 d156 d157
private abbrev d159 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 78
private theorem p159 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037184 d159 = true := by decide +kernel

private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 79
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037248 d160 = true := by decide +kernel

private def d158 : MobiusHarmonicTree := .branch 21890705 d159 d160
private def d154 : MobiusHarmonicTree := .branch 43628870 d155 d158
private def d146 : MobiusHarmonicTree := .branch 87502831 d147 d154
private def d130 : MobiusHarmonicTree := .branch 175239558 d131 d146
private abbrev d165 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 80
private theorem p165 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037312 d165 = true := by decide +kernel

private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 81
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037376 d166 = true := by decide +kernel

private def d164 : MobiusHarmonicTree := .branch 21523595 d165 d166
private abbrev d168 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 82
private theorem p168 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037440 d168 = true := by decide +kernel

private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 83
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037504 d169 = true := by decide +kernel

private def d167 : MobiusHarmonicTree := .branch 23187438 d168 d169
private def d163 : MobiusHarmonicTree := .branch 44711033 d164 d167
private abbrev d172 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 84
private theorem p172 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037568 d172 = true := by decide +kernel

private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 85
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037632 d173 = true := by decide +kernel

private def d171 : MobiusHarmonicTree := .branch 23755124 d172 d173
private abbrev d175 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 86
private theorem p175 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037696 d175 = true := by decide +kernel

private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 87
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037760 d176 = true := by decide +kernel

private def d174 : MobiusHarmonicTree := .branch 24874781 d175 d176
private def d170 : MobiusHarmonicTree := .branch 48629905 d171 d174
private def d162 : MobiusHarmonicTree := .branch 93340938 d163 d170
private abbrev d180 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 88
private theorem p180 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037824 d180 = true := by decide +kernel

private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 89
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037888 d181 = true := by decide +kernel

private def d179 : MobiusHarmonicTree := .branch 25996143 d180 d181
private abbrev d183 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 90
private theorem p183 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1037952 d183 = true := by decide +kernel

private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 91
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038016 d184 = true := by decide +kernel

private def d182 : MobiusHarmonicTree := .branch 25081593 d183 d184
private def d178 : MobiusHarmonicTree := .branch 51077736 d179 d182
private abbrev d187 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 92
private theorem p187 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038080 d187 = true := by decide +kernel

private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 93
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038144 d188 = true := by decide +kernel

private def d186 : MobiusHarmonicTree := .branch 25084257 d187 d188
private abbrev d190 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 94
private theorem p190 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038208 d190 = true := by decide +kernel

private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 95
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038272 d191 = true := by decide +kernel

private def d189 : MobiusHarmonicTree := .branch 25265127 d190 d191
private def d185 : MobiusHarmonicTree := .branch 50349384 d186 d189
private def d177 : MobiusHarmonicTree := .branch 101427120 d178 d185
private def d161 : MobiusHarmonicTree := .branch 194768058 d162 d177
private def d129 : MobiusHarmonicTree := .branch 370007616 d130 d161
private abbrev d197 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 96
private theorem p197 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038336 d197 = true := by decide +kernel

private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 97
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038400 d198 = true := by decide +kernel

private def d196 : MobiusHarmonicTree := .branch 25985231 d197 d198
private abbrev d200 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 98
private theorem p200 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038464 d200 = true := by decide +kernel

private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 99
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038528 d201 = true := by decide +kernel

private def d199 : MobiusHarmonicTree := .branch 26910278 d200 d201
private def d195 : MobiusHarmonicTree := .branch 52895509 d196 d199
private abbrev d204 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 100
private theorem p204 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038592 d204 = true := by decide +kernel

private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 101
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038656 d205 = true := by decide +kernel

private def d203 : MobiusHarmonicTree := .branch 26821283 d204 d205
private abbrev d207 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 102
private theorem p207 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038720 d207 = true := by decide +kernel

private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 103
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038784 d208 = true := by decide +kernel

private def d206 : MobiusHarmonicTree := .branch 27135642 d207 d208
private def d202 : MobiusHarmonicTree := .branch 53956925 d203 d206
private def d194 : MobiusHarmonicTree := .branch 106852434 d195 d202
private abbrev d212 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 104
private theorem p212 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038848 d212 = true := by decide +kernel

private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 105
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038912 d213 = true := by decide +kernel

private def d211 : MobiusHarmonicTree := .branch 27135195 d212 d213
private abbrev d215 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 106
private theorem p215 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1038976 d215 = true := by decide +kernel

private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 107
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039040 d216 = true := by decide +kernel

private def d214 : MobiusHarmonicTree := .branch 27652528 d215 d216
private def d210 : MobiusHarmonicTree := .branch 54787723 d211 d214
private abbrev d219 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 108
private theorem p219 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039104 d219 = true := by decide +kernel

private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 109
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039168 d220 = true := by decide +kernel

private def d218 : MobiusHarmonicTree := .branch 28248630 d219 d220
private abbrev d222 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 110
private theorem p222 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039232 d222 = true := by decide +kernel

private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 111
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039296 d223 = true := by decide +kernel

private def d221 : MobiusHarmonicTree := .branch 29566237 d222 d223
private def d217 : MobiusHarmonicTree := .branch 57814867 d218 d221
private def d209 : MobiusHarmonicTree := .branch 112602590 d210 d217
private def d193 : MobiusHarmonicTree := .branch 219455024 d194 d209
private abbrev d228 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 112
private theorem p228 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039360 d228 = true := by decide +kernel

private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 113
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039424 d229 = true := by decide +kernel

private def d227 : MobiusHarmonicTree := .branch 29784854 d228 d229
private abbrev d231 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 114
private theorem p231 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039488 d231 = true := by decide +kernel

private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 115
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039552 d232 = true := by decide +kernel

private def d230 : MobiusHarmonicTree := .branch 29384848 d231 d232
private def d226 : MobiusHarmonicTree := .branch 59169702 d227 d230
private abbrev d235 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 116
private theorem p235 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039616 d235 = true := by decide +kernel

private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 117
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039680 d236 = true := by decide +kernel

private def d234 : MobiusHarmonicTree := .branch 30090102 d235 d236
private abbrev d238 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 118
private theorem p238 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039744 d238 = true := by decide +kernel

private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 119
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039808 d239 = true := by decide +kernel

private def d237 : MobiusHarmonicTree := .branch 31475115 d238 d239
private def d233 : MobiusHarmonicTree := .branch 61565217 d234 d237
private def d225 : MobiusHarmonicTree := .branch 120734919 d226 d233
private abbrev d243 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 120
private theorem p243 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039872 d243 = true := by decide +kernel

private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 121
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1039936 d244 = true := by decide +kernel

private def d242 : MobiusHarmonicTree := .branch 31901088 d243 d244
private abbrev d246 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 122
private theorem p246 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040000 d246 = true := by decide +kernel

private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 123
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040064 d247 = true := by decide +kernel

private def d245 : MobiusHarmonicTree := .branch 31797175 d246 d247
private def d241 : MobiusHarmonicTree := .branch 63698263 d242 d245
private abbrev d250 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 124
private theorem p250 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040128 d250 = true := by decide +kernel

private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 125
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040192 d251 = true := by decide +kernel

private def d249 : MobiusHarmonicTree := .branch 30779019 d250 d251
private abbrev d253 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 126
private theorem p253 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040256 d253 = true := by decide +kernel

private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock126 127
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 1040320 d254 = true := by decide +kernel

private def d252 : MobiusHarmonicTree := .branch 31097245 d253 d254
private def d248 : MobiusHarmonicTree := .branch 61876264 d249 d252
private def d240 : MobiusHarmonicTree := .branch 125574527 d241 d248
private def d224 : MobiusHarmonicTree := .branch 246309446 d225 d240
private def d192 : MobiusHarmonicTree := .branch 465764470 d193 d224
private def d128 : MobiusHarmonicTree := .branch 835772086 d129 d192
private def d0 : MobiusHarmonicTree := .branch 1417218722 d1 d128

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 8 1032192 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 1032192 1417218722 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1032192 581446636 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1032192 255830189 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1032192 114831246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1032192 50752804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1032192 23148981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1032192 11677427 _ _ (by decide) p7 p8 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1032320 11471554 _ _ (by decide) p10 p11 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1032448 27603823 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1032448 13234761 _ _ (by decide) p14 p15 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1032576 14369062 _ _ (by decide) p17 p18 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1032704 64078442 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1032704 29596315 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1032704 14032259 _ _ (by decide) p22 p23 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1032832 15564056 _ _ (by decide) p25 p26 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1032960 34482127 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1032960 16797351 _ _ (by decide) p29 p30 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1033088 17684776 _ _ (by decide) p32 p33 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1033216 140998943 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1033216 70123572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1033216 36511759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1033216 18712326 _ _ (by decide) p38 p39 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1033344 17799433 _ _ (by decide) p41 p42 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1033472 33611813 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1033472 16880978 _ _ (by decide) p45 p46 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1033600 16730835 _ _ (by decide) p48 p49 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1033728 70875371 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1033728 34232186 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1033728 17056709 _ _ (by decide) p53 p54 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1033856 17175477 _ _ (by decide) p56 p57 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1033984 36643185 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1033984 18385087 _ _ (by decide) p60 p61 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1034112 18258098 _ _ (by decide) p63 p64 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1034240 325616447 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1034240 151658849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1034240 69036410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1034240 33401250 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1034240 16942871 _ _ (by decide) p70 p71 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1034368 16458379 _ _ (by decide) p73 p74 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1034496 35635160 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1034496 16903872 _ _ (by decide) p77 p78 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1034624 18731288 _ _ (by decide) p80 p81 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1034752 82622439 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1034752 40311056 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1034752 19882832 _ _ (by decide) p85 p86 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1034880 20428224 _ _ (by decide) p88 p89 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1035008 42311383 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1035008 20507816 _ _ (by decide) p92 p93 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1035136 21803567 _ _ (by decide) p95 p96 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1035264 173957598 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1035264 86301214 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1035264 44358261 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1035264 22302197 _ _ (by decide) p101 p102 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1035392 22056064 _ _ (by decide) p104 p105 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1035520 41942953 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1035520 20914854 _ _ (by decide) p108 p109 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1035648 21028099 _ _ (by decide) p111 p112 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1035776 87656384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1035776 45839288 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1035776 22587519 _ _ (by decide) p116 p117 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1035904 23251769 _ _ (by decide) p119 p120 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1036032 41817096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1036032 20990442 _ _ (by decide) p123 p124 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1036160 20826654 _ _ (by decide) p126 p127 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 1036288 835772086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1036288 370007616 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1036288 175239558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1036288 87736727 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1036288 42907574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1036288 21033462 _ _ (by decide) p134 p135 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1036416 21874112 _ _ (by decide) p137 p138 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1036544 44829153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1036544 22275598 _ _ (by decide) p141 p142 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1036672 22553555 _ _ (by decide) p144 p145 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1036800 87502831 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1036800 43873961 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1036800 21792713 _ _ (by decide) p149 p150 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1036928 22081248 _ _ (by decide) p152 p153 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1037056 43628870 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1037056 21738165 _ _ (by decide) p156 p157 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1037184 21890705 _ _ (by decide) p159 p160 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1037312 194768058 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1037312 93340938 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1037312 44711033 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1037312 21523595 _ _ (by decide) p165 p166 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1037440 23187438 _ _ (by decide) p168 p169 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1037568 48629905 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1037568 23755124 _ _ (by decide) p172 p173 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1037696 24874781 _ _ (by decide) p175 p176 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1037824 101427120 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1037824 51077736 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1037824 25996143 _ _ (by decide) p180 p181 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1037952 25081593 _ _ (by decide) p183 p184 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1038080 50349384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1038080 25084257 _ _ (by decide) p187 p188 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1038208 25265127 _ _ (by decide) p190 p191 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 1038336 465764470 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1038336 219455024 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1038336 106852434 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1038336 52895509 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1038336 25985231 _ _ (by decide) p197 p198 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1038464 26910278 _ _ (by decide) p200 p201 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1038592 53956925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1038592 26821283 _ _ (by decide) p204 p205 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1038720 27135642 _ _ (by decide) p207 p208 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1038848 112602590 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1038848 54787723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1038848 27135195 _ _ (by decide) p212 p213 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1038976 27652528 _ _ (by decide) p215 p216 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1039104 57814867 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1039104 28248630 _ _ (by decide) p219 p220 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1039232 29566237 _ _ (by decide) p222 p223 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 1039360 246309446 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1039360 120734919 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1039360 59169702 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1039360 29784854 _ _ (by decide) p228 p229 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1039488 29384848 _ _ (by decide) p231 p232 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1039616 61565217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1039616 30090102 _ _ (by decide) p235 p236 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1039744 31475115 _ _ (by decide) p238 p239 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 1039872 125574527 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1039872 63698263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1039872 31901088 _ _ (by decide) p243 p244 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1040000 31797175 _ _ (by decide) p246 p247 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 1040128 61876264 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1040128 30779019 _ _ (by decide) p250 p251 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 1040256 31097245 _ _ (by decide) p253 p254 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 8 1032192 mobiusHarmonicBlock126 = true := Helfgott.combined

#print axioms solution
