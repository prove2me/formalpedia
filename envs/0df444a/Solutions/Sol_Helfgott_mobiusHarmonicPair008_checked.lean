-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair008_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:19:25.004187+00:00
-- url     : https://prove2.me/submissions/5d55530f-3809-470a-a952-d5db4917fc37

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131072 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131136 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 16075603 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131200 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131264 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 5531811 d11 d12
private def d6 : MobiusHarmonicTree := .branch 21607414 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131328 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131392 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 8409418 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131456 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131520 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 6159322 d18 d19
private def d13 : MobiusHarmonicTree := .branch 14568740 d14 d17
private def d5 : MobiusHarmonicTree := .branch 36176154 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131584 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131648 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 2316749 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131712 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131776 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 3892448 d26 d27
private def d21 : MobiusHarmonicTree := .branch 6209197 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131840 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131904 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 6239504 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 131968 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132032 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 2203985 d33 d34
private def d28 : MobiusHarmonicTree := .branch 8443489 d29 d32
private def d20 : MobiusHarmonicTree := .branch 14652686 d21 d28
private def d4 : MobiusHarmonicTree := .branch 50828840 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132096 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132160 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 6234697 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132224 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132288 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 2789481 d42 d43
private def d37 : MobiusHarmonicTree := .branch 9024178 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132352 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132416 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 5671013 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132480 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132544 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 12606593 d49 d50
private def d44 : MobiusHarmonicTree := .branch 18277606 d45 d48
private def d36 : MobiusHarmonicTree := .branch 27301784 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132608 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132672 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 23583783 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132736 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132800 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 29676294 d57 d58
private def d52 : MobiusHarmonicTree := .branch 53260077 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132864 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132928 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 37876719 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 132992 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133056 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 43230641 d64 d65
private def d59 : MobiusHarmonicTree := .branch 81107360 d60 d63
private def d51 : MobiusHarmonicTree := .branch 134367437 d52 d59
private def d35 : MobiusHarmonicTree := .branch 161669221 d36 d51
private def d3 : MobiusHarmonicTree := .branch 212498061 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133120 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133184 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 40365639 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133248 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133312 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 42111811 d74 d75
private def d69 : MobiusHarmonicTree := .branch 82477450 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133376 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133440 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 42401424 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133504 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133568 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 34769543 d81 d82
private def d76 : MobiusHarmonicTree := .branch 77170967 d77 d80
private def d68 : MobiusHarmonicTree := .branch 159648417 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133632 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133696 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 37016610 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133760 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133824 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 32774821 d89 d90
private def d84 : MobiusHarmonicTree := .branch 69791431 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133888 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 133952 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 13528134 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134016 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134080 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 10963729 d96 d97
private def d91 : MobiusHarmonicTree := .branch 24491863 d92 d95
private def d83 : MobiusHarmonicTree := .branch 94283294 d84 d91
private def d67 : MobiusHarmonicTree := .branch 253931711 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134144 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134208 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 18313690 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134272 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134336 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 24341964 d105 d106
private def d100 : MobiusHarmonicTree := .branch 42655654 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134400 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134464 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 14235366 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134528 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134592 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 8061613 d112 d113
private def d107 : MobiusHarmonicTree := .branch 22296979 d108 d111
private def d99 : MobiusHarmonicTree := .branch 64952633 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134656 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134720 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 7742022 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134784 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134848 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 2002644 d120 d121
private def d115 : MobiusHarmonicTree := .branch 9744666 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134912 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 134976 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 3607735 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135040 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135104 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 6343512 d127 d128
private def d122 : MobiusHarmonicTree := .branch 9951247 d123 d126
private def d114 : MobiusHarmonicTree := .branch 19695913 d115 d122
private def d98 : MobiusHarmonicTree := .branch 84648546 d99 d114
private def d66 : MobiusHarmonicTree := .branch 338580257 d67 d98
private def d2 : MobiusHarmonicTree := .branch 551078318 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135168 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135232 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 6300325 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135296 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135360 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 7284350 d138 d139
private def d133 : MobiusHarmonicTree := .branch 13584675 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135424 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135488 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 2664897 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135552 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135616 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 4963131 d145 d146
private def d140 : MobiusHarmonicTree := .branch 7628028 d141 d144
private def d132 : MobiusHarmonicTree := .branch 21212703 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135680 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135744 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 5885930 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135808 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135872 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 9302645 d153 d154
private def d148 : MobiusHarmonicTree := .branch 15188575 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 135936 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136000 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 8345749 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136064 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136128 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 15756806 d160 d161
private def d155 : MobiusHarmonicTree := .branch 24102555 d156 d159
private def d147 : MobiusHarmonicTree := .branch 39291130 d148 d155
private def d131 : MobiusHarmonicTree := .branch 60503833 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136192 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136256 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 16960941 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136320 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136384 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 23110133 d169 d170
private def d164 : MobiusHarmonicTree := .branch 40071074 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136448 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136512 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 31235349 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136576 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136640 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 34733928 d176 d177
private def d171 : MobiusHarmonicTree := .branch 65969277 d172 d175
private def d163 : MobiusHarmonicTree := .branch 106040351 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136704 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136768 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 42224173 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136832 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136896 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 51761529 d184 d185
private def d179 : MobiusHarmonicTree := .branch 93985702 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 136960 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137024 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 49036503 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137088 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137152 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 52233158 d191 d192
private def d186 : MobiusHarmonicTree := .branch 101269661 d187 d190
private def d178 : MobiusHarmonicTree := .branch 195255363 d179 d186
private def d162 : MobiusHarmonicTree := .branch 301295714 d163 d178
private def d130 : MobiusHarmonicTree := .branch 361799547 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137216 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137280 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 60708025 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137344 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137408 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 69100071 d201 d202
private def d196 : MobiusHarmonicTree := .branch 129808096 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137472 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137536 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 72461728 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137600 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137664 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 74406220 d208 d209
private def d203 : MobiusHarmonicTree := .branch 146867948 d204 d207
private def d195 : MobiusHarmonicTree := .branch 276676044 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137728 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137792 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 74351678 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137856 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137920 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 71121754 d216 d217
private def d211 : MobiusHarmonicTree := .branch 145473432 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 137984 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138048 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 75922744 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138112 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138176 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 82561544 d223 d224
private def d218 : MobiusHarmonicTree := .branch 158484288 d219 d222
private def d210 : MobiusHarmonicTree := .branch 303957720 d211 d218
private def d194 : MobiusHarmonicTree := .branch 580633764 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138240 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138304 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 82051310 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138368 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138432 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 86526309 d232 d233
private def d227 : MobiusHarmonicTree := .branch 168577619 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138496 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138560 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 88090888 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138624 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138688 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 96706649 d239 d240
private def d234 : MobiusHarmonicTree := .branch 184797537 d235 d238
private def d226 : MobiusHarmonicTree := .branch 353375156 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138752 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138816 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 94853161 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138880 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 138944 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 88626540 d247 d248
private def d242 : MobiusHarmonicTree := .branch 183479701 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139008 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139072 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 82741540 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139136 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock016 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139200 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 89245834 d254 d255
private def d249 : MobiusHarmonicTree := .branch 171987374 d250 d253
private def d241 : MobiusHarmonicTree := .branch 355467075 d242 d249
private def d225 : MobiusHarmonicTree := .branch 708842231 d226 d241
private def d193 : MobiusHarmonicTree := .branch 1289475995 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1651275542 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2202353860 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139264 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139328 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 94467320 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139392 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139456 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 97271701 d266 d267
private def d261 : MobiusHarmonicTree := .branch 191739021 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139520 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139584 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 88786083 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139648 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139712 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 80122698 d273 d274
private def d268 : MobiusHarmonicTree := .branch 168908781 d269 d272
private def d260 : MobiusHarmonicTree := .branch 360647802 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139776 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139840 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 85011759 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139904 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 139968 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 81040727 d281 d282
private def d276 : MobiusHarmonicTree := .branch 166052486 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140032 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140096 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 76098504 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140160 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140224 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 75365170 d288 d289
private def d283 : MobiusHarmonicTree := .branch 151463674 d284 d287
private def d275 : MobiusHarmonicTree := .branch 317516160 d276 d283
private def d259 : MobiusHarmonicTree := .branch 678163962 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140288 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140352 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 67416855 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140416 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140480 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 65753819 d297 d298
private def d292 : MobiusHarmonicTree := .branch 133170674 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140544 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140608 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 77811395 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140672 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140736 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 93358937 d304 d305
private def d299 : MobiusHarmonicTree := .branch 171170332 d300 d303
private def d291 : MobiusHarmonicTree := .branch 304341006 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140800 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140864 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 91763076 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140928 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 140992 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 91083839 d312 d313
private def d307 : MobiusHarmonicTree := .branch 182846915 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141056 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141120 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 87565115 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141184 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141248 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 84404706 d319 d320
private def d314 : MobiusHarmonicTree := .branch 171969821 d315 d318
private def d306 : MobiusHarmonicTree := .branch 354816736 d307 d314
private def d290 : MobiusHarmonicTree := .branch 659157742 d291 d306
private def d258 : MobiusHarmonicTree := .branch 1337321704 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141312 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141376 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 89478022 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141440 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141504 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 88393317 d329 d330
private def d324 : MobiusHarmonicTree := .branch 177871339 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141568 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141632 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 98690976 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141696 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141760 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 112634250 d336 d337
private def d331 : MobiusHarmonicTree := .branch 211325226 d332 d335
private def d323 : MobiusHarmonicTree := .branch 389196565 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141824 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141888 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 114528220 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 141952 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142016 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 107432463 d344 d345
private def d339 : MobiusHarmonicTree := .branch 221960683 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142080 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142144 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 109403519 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142208 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142272 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 102094856 d351 d352
private def d346 : MobiusHarmonicTree := .branch 211498375 d347 d350
private def d338 : MobiusHarmonicTree := .branch 433459058 d339 d346
private def d322 : MobiusHarmonicTree := .branch 822655623 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142336 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142400 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 91860612 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142464 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142528 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 95329199 d360 d361
private def d355 : MobiusHarmonicTree := .branch 187189811 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142592 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142656 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 90477793 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142720 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142784 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 73342493 d367 d368
private def d362 : MobiusHarmonicTree := .branch 163820286 d363 d366
private def d354 : MobiusHarmonicTree := .branch 351010097 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142848 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142912 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 65579712 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 142976 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143040 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 56321232 d375 d376
private def d370 : MobiusHarmonicTree := .branch 121900944 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143104 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143168 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 47273592 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143232 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143296 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 54188075 d382 d383
private def d377 : MobiusHarmonicTree := .branch 101461667 d378 d381
private def d369 : MobiusHarmonicTree := .branch 223362611 d370 d377
private def d353 : MobiusHarmonicTree := .branch 574372708 d354 d369
private def d321 : MobiusHarmonicTree := .branch 1397028331 d322 d353
private def d257 : MobiusHarmonicTree := .branch 2734350035 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143360 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143424 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 48179656 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143488 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143552 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 54447396 d393 d394
private def d388 : MobiusHarmonicTree := .branch 102627052 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143616 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143680 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 50452229 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143744 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143808 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 44018027 d400 d401
private def d395 : MobiusHarmonicTree := .branch 94470256 d396 d399
private def d387 : MobiusHarmonicTree := .branch 197097308 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143872 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 143936 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 36426657 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144000 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144064 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 35859974 d408 d409
private def d403 : MobiusHarmonicTree := .branch 72286631 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144128 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144192 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 32457025 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144256 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144320 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 34423210 d415 d416
private def d410 : MobiusHarmonicTree := .branch 66880235 d411 d414
private def d402 : MobiusHarmonicTree := .branch 139166866 d403 d410
private def d386 : MobiusHarmonicTree := .branch 336264174 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144384 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144448 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 42187376 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144512 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144576 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 45284365 d424 d425
private def d419 : MobiusHarmonicTree := .branch 87471741 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144640 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144704 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 51449834 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144768 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144832 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 47613970 d431 d432
private def d426 : MobiusHarmonicTree := .branch 99063804 d427 d430
private def d418 : MobiusHarmonicTree := .branch 186535545 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144896 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 144960 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 49214146 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145024 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145088 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 44567268 d439 d440
private def d434 : MobiusHarmonicTree := .branch 93781414 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145152 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145216 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 40339794 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145280 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145344 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 40779163 d446 d447
private def d441 : MobiusHarmonicTree := .branch 81118957 d442 d445
private def d433 : MobiusHarmonicTree := .branch 174900371 d434 d441
private def d417 : MobiusHarmonicTree := .branch 361435916 d418 d433
private def d385 : MobiusHarmonicTree := .branch 697700090 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145408 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145472 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 45190203 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145536 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145600 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 52966969 d456 d457
private def d451 : MobiusHarmonicTree := .branch 98157172 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145664 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145728 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 53044699 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145792 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145856 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 46169768 d463 d464
private def d458 : MobiusHarmonicTree := .branch 99214467 d459 d462
private def d450 : MobiusHarmonicTree := .branch 197371639 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145920 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 145984 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 38175539 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146048 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146112 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 38772121 d471 d472
private def d466 : MobiusHarmonicTree := .branch 76947660 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146176 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146240 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 37609487 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146304 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146368 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 39878810 d478 d479
private def d473 : MobiusHarmonicTree := .branch 77488297 d474 d477
private def d465 : MobiusHarmonicTree := .branch 154435957 d466 d473
private def d449 : MobiusHarmonicTree := .branch 351807596 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146432 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146496 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 40587601 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146560 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146624 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 39482924 d487 d488
private def d482 : MobiusHarmonicTree := .branch 80070525 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146688 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146752 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 34126579 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146816 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146880 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 41721039 d494 d495
private def d489 : MobiusHarmonicTree := .branch 75847618 d490 d493
private def d481 : MobiusHarmonicTree := .branch 155918143 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 146944 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147008 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 39868580 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147072 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147136 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 36164804 d502 d503
private def d497 : MobiusHarmonicTree := .branch 76033384 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147200 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147264 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 40973099 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147328 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock017 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 147392 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 50817157 d509 d510
private def d504 : MobiusHarmonicTree := .branch 91790256 d505 d508
private def d496 : MobiusHarmonicTree := .branch 167823640 d497 d504
private def d480 : MobiusHarmonicTree := .branch 323741783 d481 d496
private def d448 : MobiusHarmonicTree := .branch 675549379 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1373249469 d385 d448
private def d256 : MobiusHarmonicTree := .branch 4107599504 d257 d384
private def d0 : MobiusHarmonicTree := .branch 6309953364 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 131072 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 131072 6309953364 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 131072 2202353860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 131072 551078318 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 131072 212498061 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 131072 50828840 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 131072 36176154 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 131072 21607414 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 131072 16075603 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 131200 5531811 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 131328 14568740 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 131328 8409418 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 131456 6159322 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 131584 14652686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 131584 6209197 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 131584 2316749 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 131712 3892448 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 131840 8443489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 131840 6239504 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 131968 2203985 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 132096 161669221 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 132096 27301784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 132096 9024178 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 132096 6234697 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 132224 2789481 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 132352 18277606 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 132352 5671013 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 132480 12606593 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 132608 134367437 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 132608 53260077 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 132608 23583783 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 132736 29676294 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 132864 81107360 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 132864 37876719 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 132992 43230641 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 133120 338580257 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 133120 253931711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 133120 159648417 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 133120 82477450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 133120 40365639 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 133248 42111811 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 133376 77170967 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 133376 42401424 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 133504 34769543 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 133632 94283294 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 133632 69791431 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 133632 37016610 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 133760 32774821 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 133888 24491863 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 133888 13528134 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 134016 10963729 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 134144 84648546 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 134144 64952633 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 134144 42655654 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 134144 18313690 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 134272 24341964 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 134400 22296979 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 134400 14235366 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 134528 8061613 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 134656 19695913 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 134656 9744666 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 134656 7742022 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 134784 2002644 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 134912 9951247 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 134912 3607735 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 135040 6343512 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 135168 1651275542 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 135168 361799547 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 135168 60503833 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 135168 21212703 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 135168 13584675 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 135168 6300325 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 135296 7284350 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 135424 7628028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 135424 2664897 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 135552 4963131 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 135680 39291130 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 135680 15188575 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 135680 5885930 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 135808 9302645 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 135936 24102555 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 135936 8345749 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 136064 15756806 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 136192 301295714 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 136192 106040351 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 136192 40071074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 136192 16960941 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 136320 23110133 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 136448 65969277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 136448 31235349 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 136576 34733928 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 136704 195255363 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 136704 93985702 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 136704 42224173 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 136832 51761529 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 136960 101269661 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 136960 49036503 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 137088 52233158 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 137216 1289475995 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 137216 580633764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 137216 276676044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 137216 129808096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 137216 60708025 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 137344 69100071 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 137472 146867948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 137472 72461728 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 137600 74406220 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 137728 303957720 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 137728 145473432 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 137728 74351678 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 137856 71121754 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 137984 158484288 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 137984 75922744 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 138112 82561544 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 138240 708842231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 138240 353375156 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 138240 168577619 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 138240 82051310 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 138368 86526309 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 138496 184797537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 138496 88090888 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 138624 96706649 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 138752 355467075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 138752 183479701 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 138752 94853161 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 138880 88626540 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 139008 171987374 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 139008 82741540 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 139136 89245834 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 139264 4107599504 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 139264 2734350035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 139264 1337321704 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 139264 678163962 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 139264 360647802 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 139264 191739021 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 139264 94467320 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 139392 97271701 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 139520 168908781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 139520 88786083 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 139648 80122698 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 139776 317516160 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 139776 166052486 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 139776 85011759 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 139904 81040727 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 140032 151463674 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 140032 76098504 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 140160 75365170 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 140288 659157742 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 140288 304341006 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 140288 133170674 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 140288 67416855 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 140416 65753819 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 140544 171170332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 140544 77811395 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 140672 93358937 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 140800 354816736 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 140800 182846915 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 140800 91763076 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 140928 91083839 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 141056 171969821 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 141056 87565115 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 141184 84404706 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 141312 1397028331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 141312 822655623 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 141312 389196565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 141312 177871339 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 141312 89478022 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 141440 88393317 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 141568 211325226 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 141568 98690976 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 141696 112634250 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 141824 433459058 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 141824 221960683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 141824 114528220 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 141952 107432463 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 142080 211498375 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 142080 109403519 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 142208 102094856 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 142336 574372708 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 142336 351010097 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 142336 187189811 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 142336 91860612 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 142464 95329199 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 142592 163820286 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 142592 90477793 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 142720 73342493 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 142848 223362611 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 142848 121900944 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 142848 65579712 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 142976 56321232 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 143104 101461667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 143104 47273592 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 143232 54188075 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 143360 1373249469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 143360 697700090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 143360 336264174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 143360 197097308 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 143360 102627052 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 143360 48179656 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 143488 54447396 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 143616 94470256 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 143616 50452229 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 143744 44018027 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 143872 139166866 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 143872 72286631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 143872 36426657 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 144000 35859974 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 144128 66880235 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 144128 32457025 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 144256 34423210 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 144384 361435916 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 144384 186535545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 144384 87471741 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 144384 42187376 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 144512 45284365 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 144640 99063804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 144640 51449834 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 144768 47613970 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 144896 174900371 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 144896 93781414 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 144896 49214146 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 145024 44567268 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 145152 81118957 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 145152 40339794 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 145280 40779163 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 145408 675549379 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 145408 351807596 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 145408 197371639 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 145408 98157172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 145408 45190203 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 145536 52966969 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 145664 99214467 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 145664 53044699 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 145792 46169768 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 145920 154435957 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 145920 76947660 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 145920 38175539 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 146048 38772121 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 146176 77488297 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 146176 37609487 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 146304 39878810 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 146432 323741783 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 146432 155918143 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 146432 80070525 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 146432 40587601 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 146560 39482924 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 146688 75847618 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 146688 34126579 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 146816 41721039 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 146944 167823640 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 146944 76033384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 146944 39868580 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 147072 36164804 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 147200 91790256 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 147200 40973099 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 147328 50817157 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 131072 (MobiusHarmonicTree.branch 6309953364 mobiusHarmonicBlock016 mobiusHarmonicBlock017) = true := Helfgott.combined

#print axioms solution
