-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair050_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T00:59:53.899973+00:00
-- url     : https://prove2.me/submissions/9a7c89e2-046e-4f9b-8a1d-2b6b78bac6eb

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819200 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819264 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 12092649 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819328 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819392 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 12128578 d11 d12
private def d6 : MobiusHarmonicTree := .branch 24221227 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819456 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819520 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 12496411 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819584 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819648 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 13898691 d18 d19
private def d13 : MobiusHarmonicTree := .branch 26395102 d14 d17
private def d5 : MobiusHarmonicTree := .branch 50616329 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819712 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819776 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 16281348 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819840 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819904 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 15851934 d26 d27
private def d21 : MobiusHarmonicTree := .branch 32133282 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 819968 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820032 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 14831213 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820096 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820160 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 15893303 d33 d34
private def d28 : MobiusHarmonicTree := .branch 30724516 d29 d32
private def d20 : MobiusHarmonicTree := .branch 62857798 d21 d28
private def d4 : MobiusHarmonicTree := .branch 113474127 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820224 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820288 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 17535372 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820352 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820416 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 18428516 d42 d43
private def d37 : MobiusHarmonicTree := .branch 35963888 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820480 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820544 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 17603045 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820608 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820672 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 18282632 d49 d50
private def d44 : MobiusHarmonicTree := .branch 35885677 d45 d48
private def d36 : MobiusHarmonicTree := .branch 71849565 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820736 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820800 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 19007132 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820864 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820928 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 19670488 d57 d58
private def d52 : MobiusHarmonicTree := .branch 38677620 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 820992 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821056 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 20655152 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821120 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821184 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 22137618 d64 d65
private def d59 : MobiusHarmonicTree := .branch 42792770 d60 d63
private def d51 : MobiusHarmonicTree := .branch 81470390 d52 d59
private def d35 : MobiusHarmonicTree := .branch 153319955 d36 d51
private def d3 : MobiusHarmonicTree := .branch 266794082 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821248 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821312 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 21868752 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821376 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821440 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 22649302 d74 d75
private def d69 : MobiusHarmonicTree := .branch 44518054 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821504 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821568 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 22224669 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821632 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821696 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 23735129 d81 d82
private def d76 : MobiusHarmonicTree := .branch 45959798 d77 d80
private def d68 : MobiusHarmonicTree := .branch 90477852 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821760 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821824 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 23288496 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821888 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 821952 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 24443113 d89 d90
private def d84 : MobiusHarmonicTree := .branch 47731609 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822016 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822080 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 22794727 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822144 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822208 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 22097875 d96 d97
private def d91 : MobiusHarmonicTree := .branch 44892602 d92 d95
private def d83 : MobiusHarmonicTree := .branch 92624211 d84 d91
private def d67 : MobiusHarmonicTree := .branch 183102063 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822272 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822336 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 23643672 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822400 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822464 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 24127581 d105 d106
private def d100 : MobiusHarmonicTree := .branch 47771253 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822528 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822592 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 23636348 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822656 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822720 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 24509002 d112 d113
private def d107 : MobiusHarmonicTree := .branch 48145350 d108 d111
private def d99 : MobiusHarmonicTree := .branch 95916603 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822784 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822848 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 25769107 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822912 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 822976 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 26245072 d120 d121
private def d115 : MobiusHarmonicTree := .branch 52014179 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823040 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823104 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 25776917 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823168 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823232 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 26586736 d127 d128
private def d122 : MobiusHarmonicTree := .branch 52363653 d123 d126
private def d114 : MobiusHarmonicTree := .branch 104377832 d115 d122
private def d98 : MobiusHarmonicTree := .branch 200294435 d99 d114
private def d66 : MobiusHarmonicTree := .branch 383396498 d67 d98
private def d2 : MobiusHarmonicTree := .branch 650190580 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823296 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823360 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 25792019 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823424 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823488 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 23594818 d138 d139
private def d133 : MobiusHarmonicTree := .branch 49386837 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823552 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823616 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 25402682 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823680 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823744 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 25958355 d145 d146
private def d140 : MobiusHarmonicTree := .branch 51361037 d141 d144
private def d132 : MobiusHarmonicTree := .branch 100747874 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823808 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823872 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 27699757 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 823936 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824000 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 28318023 d153 d154
private def d148 : MobiusHarmonicTree := .branch 56017780 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824064 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824128 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 27844077 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824192 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824256 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 27822754 d160 d161
private def d155 : MobiusHarmonicTree := .branch 55666831 d156 d159
private def d147 : MobiusHarmonicTree := .branch 111684611 d148 d155
private def d131 : MobiusHarmonicTree := .branch 212432485 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824320 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824384 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 26906243 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824448 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824512 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 26556388 d169 d170
private def d164 : MobiusHarmonicTree := .branch 53462631 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824576 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824640 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 26212715 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824704 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824768 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 27907300 d176 d177
private def d171 : MobiusHarmonicTree := .branch 54120015 d172 d175
private def d163 : MobiusHarmonicTree := .branch 107582646 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824832 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824896 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 28710370 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 824960 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825024 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 29367687 d184 d185
private def d179 : MobiusHarmonicTree := .branch 58078057 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825088 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825152 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 31036803 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825216 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825280 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 30422475 d191 d192
private def d186 : MobiusHarmonicTree := .branch 61459278 d187 d190
private def d178 : MobiusHarmonicTree := .branch 119537335 d179 d186
private def d162 : MobiusHarmonicTree := .branch 227119981 d163 d178
private def d130 : MobiusHarmonicTree := .branch 439552466 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825344 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825408 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 32803246 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825472 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825536 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 32777589 d201 d202
private def d196 : MobiusHarmonicTree := .branch 65580835 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825600 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825664 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 33568197 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825728 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825792 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 34351353 d208 d209
private def d203 : MobiusHarmonicTree := .branch 67919550 d204 d207
private def d195 : MobiusHarmonicTree := .branch 133500385 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825856 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825920 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 33213983 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 825984 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826048 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 33143434 d216 d217
private def d211 : MobiusHarmonicTree := .branch 66357417 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826112 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826176 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 33388860 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826240 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826304 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 32695061 d223 d224
private def d218 : MobiusHarmonicTree := .branch 66083921 d219 d222
private def d210 : MobiusHarmonicTree := .branch 132441338 d211 d218
private def d194 : MobiusHarmonicTree := .branch 265941723 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826368 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826432 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 32746868 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826496 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826560 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 33637071 d232 d233
private def d227 : MobiusHarmonicTree := .branch 66383939 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826624 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826688 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 35759600 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826752 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826816 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 37271994 d239 d240
private def d234 : MobiusHarmonicTree := .branch 73031594 d235 d238
private def d226 : MobiusHarmonicTree := .branch 139415533 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826880 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 826944 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 36695443 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827008 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827072 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 36941256 d247 d248
private def d242 : MobiusHarmonicTree := .branch 73636699 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827136 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827200 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 36326247 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827264 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock100 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827328 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 35727144 d254 d255
private def d249 : MobiusHarmonicTree := .branch 72053391 d250 d253
private def d241 : MobiusHarmonicTree := .branch 145690090 d242 d249
private def d225 : MobiusHarmonicTree := .branch 285105623 d226 d241
private def d193 : MobiusHarmonicTree := .branch 551047346 d194 d225
private def d129 : MobiusHarmonicTree := .branch 990599812 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1640790392 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827392 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827456 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 36012875 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827520 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827584 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 34771171 d266 d267
private def d261 : MobiusHarmonicTree := .branch 70784046 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827648 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827712 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 33998644 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827776 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827840 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 32882031 d273 d274
private def d268 : MobiusHarmonicTree := .branch 66880675 d269 d272
private def d260 : MobiusHarmonicTree := .branch 137664721 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827904 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 827968 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 32803299 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828032 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828096 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 31437268 d281 d282
private def d276 : MobiusHarmonicTree := .branch 64240567 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828160 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828224 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 30552216 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828288 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828352 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 29894363 d288 d289
private def d283 : MobiusHarmonicTree := .branch 60446579 d284 d287
private def d275 : MobiusHarmonicTree := .branch 124687146 d276 d283
private def d259 : MobiusHarmonicTree := .branch 262351867 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828416 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828480 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 30172209 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828544 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828608 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 28587764 d297 d298
private def d292 : MobiusHarmonicTree := .branch 58759973 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828672 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828736 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 29784007 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828800 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828864 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 28747861 d304 d305
private def d299 : MobiusHarmonicTree := .branch 58531868 d300 d303
private def d291 : MobiusHarmonicTree := .branch 117291841 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828928 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 828992 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 29386382 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829056 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829120 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 28889745 d312 d313
private def d307 : MobiusHarmonicTree := .branch 58276127 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829184 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829248 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 29669127 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829312 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829376 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 26639434 d319 d320
private def d314 : MobiusHarmonicTree := .branch 56308561 d315 d318
private def d306 : MobiusHarmonicTree := .branch 114584688 d307 d314
private def d290 : MobiusHarmonicTree := .branch 231876529 d291 d306
private def d258 : MobiusHarmonicTree := .branch 494228396 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829440 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829504 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 24679909 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829568 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829632 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 23298361 d329 d330
private def d324 : MobiusHarmonicTree := .branch 47978270 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829696 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829760 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 24082932 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829824 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829888 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 24134695 d336 d337
private def d331 : MobiusHarmonicTree := .branch 48217627 d332 d335
private def d323 : MobiusHarmonicTree := .branch 96195897 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 829952 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830016 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 24312826 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830080 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830144 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 24563299 d344 d345
private def d339 : MobiusHarmonicTree := .branch 48876125 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830208 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830272 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 22963646 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830336 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830400 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 22777038 d351 d352
private def d346 : MobiusHarmonicTree := .branch 45740684 d347 d350
private def d338 : MobiusHarmonicTree := .branch 94616809 d339 d346
private def d322 : MobiusHarmonicTree := .branch 190812706 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830464 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830528 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 23333432 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830592 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830656 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 24029296 d360 d361
private def d355 : MobiusHarmonicTree := .branch 47362728 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830720 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830784 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 23031334 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830848 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830912 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 23984554 d367 d368
private def d362 : MobiusHarmonicTree := .branch 47015888 d363 d366
private def d354 : MobiusHarmonicTree := .branch 94378616 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 830976 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831040 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 24389983 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831104 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831168 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 24020510 d375 d376
private def d370 : MobiusHarmonicTree := .branch 48410493 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831232 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831296 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 23013562 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831360 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831424 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 23707564 d382 d383
private def d377 : MobiusHarmonicTree := .branch 46721126 d378 d381
private def d369 : MobiusHarmonicTree := .branch 95131619 d370 d377
private def d353 : MobiusHarmonicTree := .branch 189510235 d354 d369
private def d321 : MobiusHarmonicTree := .branch 380322941 d322 d353
private def d257 : MobiusHarmonicTree := .branch 874551337 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831488 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831552 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 25634047 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831616 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831680 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 26239726 d393 d394
private def d388 : MobiusHarmonicTree := .branch 51873773 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831744 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831808 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 26751434 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831872 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 831936 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 27924117 d400 d401
private def d395 : MobiusHarmonicTree := .branch 54675551 d396 d399
private def d387 : MobiusHarmonicTree := .branch 106549324 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832000 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832064 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 26094216 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832128 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832192 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 27420434 d408 d409
private def d403 : MobiusHarmonicTree := .branch 53514650 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832256 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832320 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 27896790 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832384 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832448 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 29902240 d415 d416
private def d410 : MobiusHarmonicTree := .branch 57799030 d411 d414
private def d402 : MobiusHarmonicTree := .branch 111313680 d403 d410
private def d386 : MobiusHarmonicTree := .branch 217863004 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832512 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832576 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 30535404 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832640 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832704 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 32605884 d424 d425
private def d419 : MobiusHarmonicTree := .branch 63141288 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832768 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832832 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 32434043 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832896 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 832960 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 31921166 d431 d432
private def d426 : MobiusHarmonicTree := .branch 64355209 d427 d430
private def d418 : MobiusHarmonicTree := .branch 127496497 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833024 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833088 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 31700233 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833152 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833216 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 31287301 d439 d440
private def d434 : MobiusHarmonicTree := .branch 62987534 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833280 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833344 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 30198903 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833408 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833472 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 30205055 d446 d447
private def d441 : MobiusHarmonicTree := .branch 60403958 d442 d445
private def d433 : MobiusHarmonicTree := .branch 123391492 d434 d441
private def d417 : MobiusHarmonicTree := .branch 250887989 d418 d433
private def d385 : MobiusHarmonicTree := .branch 468750993 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833536 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833600 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 31857059 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833664 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833728 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 31880998 d456 d457
private def d451 : MobiusHarmonicTree := .branch 63738057 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833792 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833856 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 33147271 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833920 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 833984 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 33154218 d463 d464
private def d458 : MobiusHarmonicTree := .branch 66301489 d459 d462
private def d450 : MobiusHarmonicTree := .branch 130039546 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834048 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834112 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 32222360 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834176 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834240 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 31501848 d471 d472
private def d466 : MobiusHarmonicTree := .branch 63724208 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834304 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834368 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 28747640 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834432 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834496 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 27990606 d478 d479
private def d473 : MobiusHarmonicTree := .branch 56738246 d474 d477
private def d465 : MobiusHarmonicTree := .branch 120462454 d466 d473
private def d449 : MobiusHarmonicTree := .branch 250502000 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834560 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834624 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 28630935 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834688 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834752 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 28856563 d487 d488
private def d482 : MobiusHarmonicTree := .branch 57487498 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834816 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834880 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 28000548 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 834944 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835008 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 27666875 d494 d495
private def d489 : MobiusHarmonicTree := .branch 55667423 d490 d493
private def d481 : MobiusHarmonicTree := .branch 113154921 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835072 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835136 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 26698739 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835200 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835264 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 26574919 d502 d503
private def d497 : MobiusHarmonicTree := .branch 53273658 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835328 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835392 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 25633534 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835456 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock101 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 835520 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 24740417 d509 d510
private def d504 : MobiusHarmonicTree := .branch 50373951 d505 d508
private def d496 : MobiusHarmonicTree := .branch 103647609 d497 d504
private def d480 : MobiusHarmonicTree := .branch 216802530 d481 d496
private def d448 : MobiusHarmonicTree := .branch 467304530 d449 d480
private def d384 : MobiusHarmonicTree := .branch 936055523 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1810606860 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3451397252 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 819200 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 819200 3451397252 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 819200 1640790392 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 819200 650190580 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 819200 266794082 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 819200 113474127 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 819200 50616329 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 819200 24221227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 819200 12092649 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 819328 12128578 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 819456 26395102 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 819456 12496411 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 819584 13898691 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 819712 62857798 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 819712 32133282 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 819712 16281348 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 819840 15851934 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 819968 30724516 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 819968 14831213 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 820096 15893303 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 820224 153319955 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 820224 71849565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 820224 35963888 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 820224 17535372 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 820352 18428516 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 820480 35885677 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 820480 17603045 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 820608 18282632 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 820736 81470390 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 820736 38677620 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 820736 19007132 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 820864 19670488 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 820992 42792770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 820992 20655152 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 821120 22137618 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 821248 383396498 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 821248 183102063 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 821248 90477852 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 821248 44518054 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 821248 21868752 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 821376 22649302 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 821504 45959798 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 821504 22224669 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 821632 23735129 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 821760 92624211 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 821760 47731609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 821760 23288496 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 821888 24443113 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 822016 44892602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 822016 22794727 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 822144 22097875 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 822272 200294435 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 822272 95916603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 822272 47771253 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 822272 23643672 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 822400 24127581 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 822528 48145350 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 822528 23636348 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 822656 24509002 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 822784 104377832 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 822784 52014179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 822784 25769107 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 822912 26245072 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 823040 52363653 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 823040 25776917 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 823168 26586736 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 823296 990599812 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 823296 439552466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 823296 212432485 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 823296 100747874 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 823296 49386837 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 823296 25792019 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 823424 23594818 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 823552 51361037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 823552 25402682 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 823680 25958355 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 823808 111684611 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 823808 56017780 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 823808 27699757 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 823936 28318023 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 824064 55666831 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 824064 27844077 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 824192 27822754 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 824320 227119981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 824320 107582646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 824320 53462631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 824320 26906243 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 824448 26556388 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 824576 54120015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 824576 26212715 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 824704 27907300 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 824832 119537335 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 824832 58078057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 824832 28710370 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 824960 29367687 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 825088 61459278 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 825088 31036803 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 825216 30422475 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 825344 551047346 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 825344 265941723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 825344 133500385 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 825344 65580835 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 825344 32803246 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 825472 32777589 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 825600 67919550 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 825600 33568197 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 825728 34351353 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 825856 132441338 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 825856 66357417 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 825856 33213983 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 825984 33143434 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 826112 66083921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 826112 33388860 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 826240 32695061 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 826368 285105623 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 826368 139415533 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 826368 66383939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 826368 32746868 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 826496 33637071 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 826624 73031594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 826624 35759600 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 826752 37271994 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 826880 145690090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 826880 73636699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 826880 36695443 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 827008 36941256 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 827136 72053391 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 827136 36326247 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 827264 35727144 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 827392 1810606860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 827392 874551337 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 827392 494228396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 827392 262351867 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 827392 137664721 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 827392 70784046 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 827392 36012875 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 827520 34771171 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 827648 66880675 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 827648 33998644 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 827776 32882031 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 827904 124687146 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 827904 64240567 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 827904 32803299 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 828032 31437268 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 828160 60446579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 828160 30552216 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 828288 29894363 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 828416 231876529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 828416 117291841 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 828416 58759973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 828416 30172209 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 828544 28587764 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 828672 58531868 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 828672 29784007 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 828800 28747861 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 828928 114584688 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 828928 58276127 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 828928 29386382 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 829056 28889745 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 829184 56308561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 829184 29669127 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 829312 26639434 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 829440 380322941 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 829440 190812706 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 829440 96195897 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 829440 47978270 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 829440 24679909 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 829568 23298361 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 829696 48217627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 829696 24082932 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 829824 24134695 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 829952 94616809 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 829952 48876125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 829952 24312826 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 830080 24563299 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 830208 45740684 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 830208 22963646 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 830336 22777038 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 830464 189510235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 830464 94378616 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 830464 47362728 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 830464 23333432 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 830592 24029296 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 830720 47015888 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 830720 23031334 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 830848 23984554 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 830976 95131619 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 830976 48410493 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 830976 24389983 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 831104 24020510 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 831232 46721126 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 831232 23013562 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 831360 23707564 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 831488 936055523 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 831488 468750993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 831488 217863004 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 831488 106549324 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 831488 51873773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 831488 25634047 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 831616 26239726 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 831744 54675551 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 831744 26751434 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 831872 27924117 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 832000 111313680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 832000 53514650 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 832000 26094216 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 832128 27420434 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 832256 57799030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 832256 27896790 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 832384 29902240 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 832512 250887989 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 832512 127496497 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 832512 63141288 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 832512 30535404 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 832640 32605884 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 832768 64355209 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 832768 32434043 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 832896 31921166 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 833024 123391492 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 833024 62987534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 833024 31700233 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 833152 31287301 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 833280 60403958 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 833280 30198903 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 833408 30205055 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 833536 467304530 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 833536 250502000 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 833536 130039546 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 833536 63738057 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 833536 31857059 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 833664 31880998 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 833792 66301489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 833792 33147271 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 833920 33154218 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 834048 120462454 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 834048 63724208 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 834048 32222360 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 834176 31501848 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 834304 56738246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 834304 28747640 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 834432 27990606 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 834560 216802530 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 834560 113154921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 834560 57487498 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 834560 28630935 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 834688 28856563 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 834816 55667423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 834816 28000548 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 834944 27666875 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 835072 103647609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 835072 53273658 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 835072 26698739 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 835200 26574919 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 835328 50373951 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 835328 25633534 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 835456 24740417 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 819200 (MobiusHarmonicTree.branch 3451397252 mobiusHarmonicBlock100 mobiusHarmonicBlock101) = true := Helfgott.combined

#print axioms solution
