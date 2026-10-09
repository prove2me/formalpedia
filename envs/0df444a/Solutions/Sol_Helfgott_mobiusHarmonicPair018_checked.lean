-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair018_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:57:06.151621+00:00
-- url     : https://prove2.me/submissions/6c4657d8-d611-44db-bb59-d72610cb342f

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294912 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 294976 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 59825299 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295040 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295104 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 59541627 d11 d12
private def d6 : MobiusHarmonicTree := .branch 119366926 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295168 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295232 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 61494254 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295296 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295360 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 61545206 d18 d19
private def d13 : MobiusHarmonicTree := .branch 123039460 d14 d17
private def d5 : MobiusHarmonicTree := .branch 242406386 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295424 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295488 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 66578025 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295552 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295616 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 68988122 d26 d27
private def d21 : MobiusHarmonicTree := .branch 135566147 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295680 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295744 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 71044718 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295808 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295872 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 67313317 d33 d34
private def d28 : MobiusHarmonicTree := .branch 138358035 d29 d32
private def d20 : MobiusHarmonicTree := .branch 273924182 d21 d28
private def d4 : MobiusHarmonicTree := .branch 516330568 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 295936 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296000 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 63216643 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296064 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296128 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 65019130 d42 d43
private def d37 : MobiusHarmonicTree := .branch 128235773 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296192 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296256 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 65116528 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296320 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296384 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 65391414 d49 d50
private def d44 : MobiusHarmonicTree := .branch 130507942 d45 d48
private def d36 : MobiusHarmonicTree := .branch 258743715 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296448 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296512 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 67113942 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296576 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296640 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 62298002 d57 d58
private def d52 : MobiusHarmonicTree := .branch 129411944 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296704 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296768 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 60666997 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296832 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296896 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 62941258 d64 d65
private def d59 : MobiusHarmonicTree := .branch 123608255 d60 d63
private def d51 : MobiusHarmonicTree := .branch 253020199 d52 d59
private def d35 : MobiusHarmonicTree := .branch 511763914 d36 d51
private def d3 : MobiusHarmonicTree := .branch 1028094482 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 296960 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297024 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 64722142 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297088 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297152 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 68877200 d74 d75
private def d69 : MobiusHarmonicTree := .branch 133599342 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297216 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297280 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 70395073 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297344 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297408 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 74634968 d81 d82
private def d76 : MobiusHarmonicTree := .branch 145030041 d77 d80
private def d68 : MobiusHarmonicTree := .branch 278629383 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297472 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297536 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 80514588 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297600 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297664 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 81961797 d89 d90
private def d84 : MobiusHarmonicTree := .branch 162476385 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297728 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297792 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 85841893 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297856 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297920 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 84895588 d96 d97
private def d91 : MobiusHarmonicTree := .branch 170737481 d92 d95
private def d83 : MobiusHarmonicTree := .branch 333213866 d84 d91
private def d67 : MobiusHarmonicTree := .branch 611843249 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 297984 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298048 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 81708586 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298112 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298176 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 83407151 d105 d106
private def d100 : MobiusHarmonicTree := .branch 165115737 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298240 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298304 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 87491396 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298368 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298432 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 83902252 d112 d113
private def d107 : MobiusHarmonicTree := .branch 171393648 d108 d111
private def d99 : MobiusHarmonicTree := .branch 336509385 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298496 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298560 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 86471729 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298624 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298688 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 88748501 d120 d121
private def d115 : MobiusHarmonicTree := .branch 175220230 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298752 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298816 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 86812871 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298880 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 298944 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 90291137 d127 d128
private def d122 : MobiusHarmonicTree := .branch 177104008 d123 d126
private def d114 : MobiusHarmonicTree := .branch 352324238 d115 d122
private def d98 : MobiusHarmonicTree := .branch 688833623 d99 d114
private def d66 : MobiusHarmonicTree := .branch 1300676872 d67 d98
private def d2 : MobiusHarmonicTree := .branch 2328771354 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299008 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299072 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 94224955 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299136 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299200 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 97396571 d138 d139
private def d133 : MobiusHarmonicTree := .branch 191621526 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299264 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299328 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 98069960 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299392 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299456 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 97423596 d145 d146
private def d140 : MobiusHarmonicTree := .branch 195493556 d141 d144
private def d132 : MobiusHarmonicTree := .branch 387115082 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299520 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299584 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 95819849 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299648 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299712 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 94934907 d153 d154
private def d148 : MobiusHarmonicTree := .branch 190754756 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299776 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299840 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 95794633 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299904 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 299968 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 94393680 d160 d161
private def d155 : MobiusHarmonicTree := .branch 190188313 d156 d159
private def d147 : MobiusHarmonicTree := .branch 380943069 d148 d155
private def d131 : MobiusHarmonicTree := .branch 768058151 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300032 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300096 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 95249812 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300160 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300224 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 96914306 d169 d170
private def d164 : MobiusHarmonicTree := .branch 192164118 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300288 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300352 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 98601252 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300416 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300480 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 99297979 d176 d177
private def d171 : MobiusHarmonicTree := .branch 197899231 d172 d175
private def d163 : MobiusHarmonicTree := .branch 390063349 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300544 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300608 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 99611740 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300672 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300736 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 98485515 d184 d185
private def d179 : MobiusHarmonicTree := .branch 198097255 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300800 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300864 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 94720876 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300928 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 300992 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 86408014 d191 d192
private def d186 : MobiusHarmonicTree := .branch 181128890 d187 d190
private def d178 : MobiusHarmonicTree := .branch 379226145 d179 d186
private def d162 : MobiusHarmonicTree := .branch 769289494 d163 d178
private def d130 : MobiusHarmonicTree := .branch 1537347645 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301056 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301120 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 84776844 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301184 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301248 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 84449072 d201 d202
private def d196 : MobiusHarmonicTree := .branch 169225916 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301312 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301376 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 81373744 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301440 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301504 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 82310884 d208 d209
private def d203 : MobiusHarmonicTree := .branch 163684628 d204 d207
private def d195 : MobiusHarmonicTree := .branch 332910544 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301568 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301632 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 80572021 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301696 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301760 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 79344679 d216 d217
private def d211 : MobiusHarmonicTree := .branch 159916700 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301824 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301888 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 78383784 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 301952 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302016 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 75757767 d223 d224
private def d218 : MobiusHarmonicTree := .branch 154141551 d219 d222
private def d210 : MobiusHarmonicTree := .branch 314058251 d211 d218
private def d194 : MobiusHarmonicTree := .branch 646968795 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302080 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302144 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 76897349 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302208 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302272 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 70642024 d232 d233
private def d227 : MobiusHarmonicTree := .branch 147539373 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302336 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302400 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 72116510 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302464 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302528 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 71157246 d239 d240
private def d234 : MobiusHarmonicTree := .branch 143273756 d235 d238
private def d226 : MobiusHarmonicTree := .branch 290813129 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302592 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302656 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 65748165 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302720 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302784 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 67203113 d247 d248
private def d242 : MobiusHarmonicTree := .branch 132951278 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302848 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302912 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 67785699 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 302976 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock036 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303040 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 67265110 d254 d255
private def d249 : MobiusHarmonicTree := .branch 135050809 d250 d253
private def d241 : MobiusHarmonicTree := .branch 268002087 d242 d249
private def d225 : MobiusHarmonicTree := .branch 558815216 d226 d241
private def d193 : MobiusHarmonicTree := .branch 1205784011 d194 d225
private def d129 : MobiusHarmonicTree := .branch 2743131656 d130 d193
private def d1 : MobiusHarmonicTree := .branch 5071903010 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303104 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303168 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 70891455 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303232 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303296 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 75573219 d266 d267
private def d261 : MobiusHarmonicTree := .branch 146464674 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303360 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303424 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 77993346 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303488 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303552 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 74188698 d273 d274
private def d268 : MobiusHarmonicTree := .branch 152182044 d269 d272
private def d260 : MobiusHarmonicTree := .branch 298646718 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303616 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303680 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 71183857 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303744 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303808 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 66690128 d281 d282
private def d276 : MobiusHarmonicTree := .branch 137873985 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303872 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 303936 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 69501646 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304000 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304064 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 68002353 d288 d289
private def d283 : MobiusHarmonicTree := .branch 137503999 d284 d287
private def d275 : MobiusHarmonicTree := .branch 275377984 d276 d283
private def d259 : MobiusHarmonicTree := .branch 574024702 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304128 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304192 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 70070946 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304256 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304320 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 66828082 d297 d298
private def d292 : MobiusHarmonicTree := .branch 136899028 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304384 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304448 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 67049311 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304512 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304576 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 70432197 d304 d305
private def d299 : MobiusHarmonicTree := .branch 137481508 d300 d303
private def d291 : MobiusHarmonicTree := .branch 274380536 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304640 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304704 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 76083916 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304768 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304832 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 78272765 d312 d313
private def d307 : MobiusHarmonicTree := .branch 154356681 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304896 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 304960 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 75170898 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305024 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305088 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 71468055 d319 d320
private def d314 : MobiusHarmonicTree := .branch 146638953 d315 d318
private def d306 : MobiusHarmonicTree := .branch 300995634 d307 d314
private def d290 : MobiusHarmonicTree := .branch 575376170 d291 d306
private def d258 : MobiusHarmonicTree := .branch 1149400872 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305152 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305216 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 73882212 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305280 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305344 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 74290396 d329 d330
private def d324 : MobiusHarmonicTree := .branch 148172608 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305408 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305472 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 70222693 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305536 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305600 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 68779653 d336 d337
private def d331 : MobiusHarmonicTree := .branch 139002346 d332 d335
private def d323 : MobiusHarmonicTree := .branch 287174954 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305664 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305728 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 70026539 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305792 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305856 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 66855258 d344 d345
private def d339 : MobiusHarmonicTree := .branch 136881797 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305920 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 305984 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 66549381 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306048 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306112 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 67423094 d351 d352
private def d346 : MobiusHarmonicTree := .branch 133972475 d347 d350
private def d338 : MobiusHarmonicTree := .branch 270854272 d339 d346
private def d322 : MobiusHarmonicTree := .branch 558029226 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306176 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306240 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 71013043 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306304 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306368 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 69697671 d360 d361
private def d355 : MobiusHarmonicTree := .branch 140710714 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306432 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306496 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 66327322 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306560 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306624 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 70682764 d367 d368
private def d362 : MobiusHarmonicTree := .branch 137010086 d363 d366
private def d354 : MobiusHarmonicTree := .branch 277720800 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306688 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306752 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 71455399 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306816 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306880 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 68805576 d375 d376
private def d370 : MobiusHarmonicTree := .branch 140260975 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 306944 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307008 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 70486749 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307072 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307136 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 70848464 d382 d383
private def d377 : MobiusHarmonicTree := .branch 141335213 d378 d381
private def d369 : MobiusHarmonicTree := .branch 281596188 d370 d377
private def d353 : MobiusHarmonicTree := .branch 559316988 d354 d369
private def d321 : MobiusHarmonicTree := .branch 1117346214 d322 d353
private def d257 : MobiusHarmonicTree := .branch 2266747086 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307200 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307264 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 67785561 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307328 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307392 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 68671486 d393 d394
private def d388 : MobiusHarmonicTree := .branch 136457047 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307456 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307520 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 68106413 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307584 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307648 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 65493864 d400 d401
private def d395 : MobiusHarmonicTree := .branch 133600277 d396 d399
private def d387 : MobiusHarmonicTree := .branch 270057324 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307712 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307776 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 67227361 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307840 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307904 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 71233403 d408 d409
private def d403 : MobiusHarmonicTree := .branch 138460764 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 307968 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308032 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 73307461 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308096 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308160 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 72614966 d415 d416
private def d410 : MobiusHarmonicTree := .branch 145922427 d411 d414
private def d402 : MobiusHarmonicTree := .branch 284383191 d403 d410
private def d386 : MobiusHarmonicTree := .branch 554440515 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308224 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308288 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 71920101 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308352 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308416 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 72895014 d424 d425
private def d419 : MobiusHarmonicTree := .branch 144815115 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308480 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308544 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 74372194 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308608 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308672 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 78274088 d431 d432
private def d426 : MobiusHarmonicTree := .branch 152646282 d427 d430
private def d418 : MobiusHarmonicTree := .branch 297461397 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308736 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308800 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 78708313 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308864 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308928 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 75127785 d439 d440
private def d434 : MobiusHarmonicTree := .branch 153836098 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 308992 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309056 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 72236464 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309120 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309184 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 69201582 d446 d447
private def d441 : MobiusHarmonicTree := .branch 141438046 d442 d445
private def d433 : MobiusHarmonicTree := .branch 295274144 d434 d441
private def d417 : MobiusHarmonicTree := .branch 592735541 d418 d433
private def d385 : MobiusHarmonicTree := .branch 1147176056 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309248 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309312 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 67837984 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309376 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309440 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 63615303 d456 d457
private def d451 : MobiusHarmonicTree := .branch 131453287 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309504 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309568 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 60994975 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309632 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309696 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 60310951 d463 d464
private def d458 : MobiusHarmonicTree := .branch 121305926 d459 d462
private def d450 : MobiusHarmonicTree := .branch 252759213 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309760 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309824 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 61567364 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309888 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 309952 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 63767876 d471 d472
private def d466 : MobiusHarmonicTree := .branch 125335240 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310016 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310080 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 67231387 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310144 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310208 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 63096662 d478 d479
private def d473 : MobiusHarmonicTree := .branch 130328049 d474 d477
private def d465 : MobiusHarmonicTree := .branch 255663289 d466 d473
private def d449 : MobiusHarmonicTree := .branch 508422502 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310272 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310336 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 59419678 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310400 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310464 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 60486954 d487 d488
private def d482 : MobiusHarmonicTree := .branch 119906632 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310528 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310592 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 63314615 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310656 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310720 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 65239048 d494 d495
private def d489 : MobiusHarmonicTree := .branch 128553663 d490 d493
private def d481 : MobiusHarmonicTree := .branch 248460295 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310784 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310848 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 60631139 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310912 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 310976 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 57400170 d502 d503
private def d497 : MobiusHarmonicTree := .branch 118031309 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311040 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311104 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 61201292 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311168 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock037 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311232 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 61051279 d509 d510
private def d504 : MobiusHarmonicTree := .branch 122252571 d505 d508
private def d496 : MobiusHarmonicTree := .branch 240283880 d497 d504
private def d480 : MobiusHarmonicTree := .branch 488744175 d481 d496
private def d448 : MobiusHarmonicTree := .branch 997166677 d449 d480
private def d384 : MobiusHarmonicTree := .branch 2144342733 d385 d448
private def d256 : MobiusHarmonicTree := .branch 4411089819 d257 d384
private def d0 : MobiusHarmonicTree := .branch 9482992829 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 294912 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 294912 9482992829 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 294912 5071903010 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 294912 2328771354 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 294912 1028094482 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 294912 516330568 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 294912 242406386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 294912 119366926 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 294912 59825299 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 295040 59541627 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 295168 123039460 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 295168 61494254 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 295296 61545206 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 295424 273924182 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 295424 135566147 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 295424 66578025 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 295552 68988122 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 295680 138358035 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 295680 71044718 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 295808 67313317 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 295936 511763914 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 295936 258743715 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 295936 128235773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 295936 63216643 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 296064 65019130 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 296192 130507942 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 296192 65116528 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 296320 65391414 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 296448 253020199 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 296448 129411944 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 296448 67113942 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 296576 62298002 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 296704 123608255 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 296704 60666997 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 296832 62941258 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 296960 1300676872 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 296960 611843249 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 296960 278629383 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 296960 133599342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 296960 64722142 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 297088 68877200 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 297216 145030041 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 297216 70395073 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 297344 74634968 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 297472 333213866 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 297472 162476385 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 297472 80514588 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 297600 81961797 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 297728 170737481 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 297728 85841893 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 297856 84895588 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 297984 688833623 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 297984 336509385 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 297984 165115737 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 297984 81708586 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 298112 83407151 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 298240 171393648 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 298240 87491396 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 298368 83902252 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 298496 352324238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 298496 175220230 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 298496 86471729 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 298624 88748501 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 298752 177104008 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 298752 86812871 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 298880 90291137 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 299008 2743131656 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 299008 1537347645 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 299008 768058151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 299008 387115082 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 299008 191621526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 299008 94224955 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 299136 97396571 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 299264 195493556 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 299264 98069960 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 299392 97423596 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 299520 380943069 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 299520 190754756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 299520 95819849 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 299648 94934907 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 299776 190188313 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 299776 95794633 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 299904 94393680 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 300032 769289494 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 300032 390063349 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 300032 192164118 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 300032 95249812 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 300160 96914306 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 300288 197899231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 300288 98601252 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 300416 99297979 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 300544 379226145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 300544 198097255 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 300544 99611740 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 300672 98485515 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 300800 181128890 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 300800 94720876 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 300928 86408014 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 301056 1205784011 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 301056 646968795 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 301056 332910544 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 301056 169225916 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 301056 84776844 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 301184 84449072 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 301312 163684628 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 301312 81373744 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 301440 82310884 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 301568 314058251 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 301568 159916700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 301568 80572021 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 301696 79344679 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 301824 154141551 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 301824 78383784 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 301952 75757767 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 302080 558815216 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 302080 290813129 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 302080 147539373 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 302080 76897349 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 302208 70642024 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 302336 143273756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 302336 72116510 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 302464 71157246 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 302592 268002087 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 302592 132951278 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 302592 65748165 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 302720 67203113 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 302848 135050809 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 302848 67785699 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 302976 67265110 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 303104 4411089819 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 303104 2266747086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 303104 1149400872 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 303104 574024702 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 303104 298646718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 303104 146464674 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 303104 70891455 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 303232 75573219 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 303360 152182044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 303360 77993346 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 303488 74188698 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 303616 275377984 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 303616 137873985 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 303616 71183857 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 303744 66690128 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 303872 137503999 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 303872 69501646 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 304000 68002353 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 304128 575376170 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 304128 274380536 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 304128 136899028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 304128 70070946 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 304256 66828082 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 304384 137481508 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 304384 67049311 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 304512 70432197 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 304640 300995634 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 304640 154356681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 304640 76083916 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 304768 78272765 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 304896 146638953 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 304896 75170898 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 305024 71468055 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 305152 1117346214 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 305152 558029226 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 305152 287174954 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 305152 148172608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 305152 73882212 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 305280 74290396 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 305408 139002346 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 305408 70222693 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 305536 68779653 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 305664 270854272 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 305664 136881797 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 305664 70026539 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 305792 66855258 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 305920 133972475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 305920 66549381 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 306048 67423094 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 306176 559316988 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 306176 277720800 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 306176 140710714 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 306176 71013043 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 306304 69697671 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 306432 137010086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 306432 66327322 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 306560 70682764 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 306688 281596188 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 306688 140260975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 306688 71455399 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 306816 68805576 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 306944 141335213 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 306944 70486749 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 307072 70848464 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 307200 2144342733 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 307200 1147176056 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 307200 554440515 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 307200 270057324 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 307200 136457047 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 307200 67785561 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 307328 68671486 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 307456 133600277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 307456 68106413 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 307584 65493864 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 307712 284383191 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 307712 138460764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 307712 67227361 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 307840 71233403 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 307968 145922427 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 307968 73307461 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 308096 72614966 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 308224 592735541 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 308224 297461397 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 308224 144815115 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 308224 71920101 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 308352 72895014 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 308480 152646282 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 308480 74372194 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 308608 78274088 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 308736 295274144 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 308736 153836098 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 308736 78708313 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 308864 75127785 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 308992 141438046 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 308992 72236464 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 309120 69201582 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 309248 997166677 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 309248 508422502 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 309248 252759213 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 309248 131453287 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 309248 67837984 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 309376 63615303 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 309504 121305926 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 309504 60994975 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 309632 60310951 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 309760 255663289 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 309760 125335240 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 309760 61567364 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 309888 63767876 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 310016 130328049 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 310016 67231387 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 310144 63096662 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 310272 488744175 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 310272 248460295 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 310272 119906632 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 310272 59419678 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 310400 60486954 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 310528 128553663 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 310528 63314615 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 310656 65239048 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 310784 240283880 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 310784 118031309 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 310784 60631139 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 310912 57400170 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 311040 122252571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 311040 61201292 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 311168 61051279 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 294912 (MobiusHarmonicTree.branch 9482992829 mobiusHarmonicBlock036 mobiusHarmonicBlock037) = true := Helfgott.combined

#print axioms solution
