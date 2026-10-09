-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair010_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:28:13.694004+00:00
-- url     : https://prove2.me/submissions/234462b3-78f6-42a8-8172-8f919ce15e75

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163840 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163904 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 5435449 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 163968 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164032 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 14783424 d11 d12
private def d6 : MobiusHarmonicTree := .branch 20218873 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164096 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164160 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 14583395 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164224 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164288 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 9763285 d18 d19
private def d13 : MobiusHarmonicTree := .branch 24346680 d14 d17
private def d5 : MobiusHarmonicTree := .branch 44565553 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164352 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164416 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 8600455 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164480 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164544 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 11267184 d26 d27
private def d21 : MobiusHarmonicTree := .branch 19867639 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164608 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164672 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 13165606 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164736 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164800 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 14235289 d33 d34
private def d28 : MobiusHarmonicTree := .branch 27400895 d29 d32
private def d20 : MobiusHarmonicTree := .branch 47268534 d21 d28
private def d4 : MobiusHarmonicTree := .branch 91834087 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164864 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164928 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 20996589 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 164992 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165056 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 31964823 d42 d43
private def d37 : MobiusHarmonicTree := .branch 52961412 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165120 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165184 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 39149900 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165248 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165312 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 41830224 d49 d50
private def d44 : MobiusHarmonicTree := .branch 80980124 d45 d48
private def d36 : MobiusHarmonicTree := .branch 133941536 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165376 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165440 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 40667404 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165504 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165568 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 30846037 d57 d58
private def d52 : MobiusHarmonicTree := .branch 71513441 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165632 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165696 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 33199540 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165760 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165824 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 37383223 d64 d65
private def d59 : MobiusHarmonicTree := .branch 70582763 d60 d63
private def d51 : MobiusHarmonicTree := .branch 142096204 d52 d59
private def d35 : MobiusHarmonicTree := .branch 276037740 d36 d51
private def d3 : MobiusHarmonicTree := .branch 367871827 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165888 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 165952 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 35034344 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166016 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166080 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 37705026 d74 d75
private def d69 : MobiusHarmonicTree := .branch 72739370 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166144 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166208 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 33687093 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166272 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166336 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 27366780 d81 d82
private def d76 : MobiusHarmonicTree := .branch 61053873 d77 d80
private def d68 : MobiusHarmonicTree := .branch 133793243 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166400 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166464 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 26479617 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166528 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166592 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 31352844 d89 d90
private def d84 : MobiusHarmonicTree := .branch 57832461 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166656 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166720 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 25761577 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166784 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166848 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 26563481 d96 d97
private def d91 : MobiusHarmonicTree := .branch 52325058 d92 d95
private def d83 : MobiusHarmonicTree := .branch 110157519 d84 d91
private def d67 : MobiusHarmonicTree := .branch 243950762 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166912 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 166976 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 28213961 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167040 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167104 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 18078485 d105 d106
private def d100 : MobiusHarmonicTree := .branch 46292446 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167168 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167232 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 26759108 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167296 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167360 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 28937554 d112 d113
private def d107 : MobiusHarmonicTree := .branch 55696662 d108 d111
private def d99 : MobiusHarmonicTree := .branch 101989108 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167424 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167488 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 26778060 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167552 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167616 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 26752619 d120 d121
private def d115 : MobiusHarmonicTree := .branch 53530679 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167680 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167744 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 24531421 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167808 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167872 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 35306480 d127 d128
private def d122 : MobiusHarmonicTree := .branch 59837901 d123 d126
private def d114 : MobiusHarmonicTree := .branch 113368580 d115 d122
private def d98 : MobiusHarmonicTree := .branch 215357688 d99 d114
private def d66 : MobiusHarmonicTree := .branch 459308450 d67 d98
private def d2 : MobiusHarmonicTree := .branch 827180277 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 167936 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168000 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 46588754 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168064 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168128 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 56742067 d138 d139
private def d133 : MobiusHarmonicTree := .branch 103330821 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168192 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168256 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 57894152 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168320 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168384 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 57190394 d145 d146
private def d140 : MobiusHarmonicTree := .branch 115084546 d141 d144
private def d132 : MobiusHarmonicTree := .branch 218415367 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168448 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168512 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 60061369 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168576 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168640 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 66217437 d153 d154
private def d148 : MobiusHarmonicTree := .branch 126278806 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168704 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168768 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 73129828 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168832 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168896 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 80683044 d160 d161
private def d155 : MobiusHarmonicTree := .branch 153812872 d156 d159
private def d147 : MobiusHarmonicTree := .branch 280091678 d148 d155
private def d131 : MobiusHarmonicTree := .branch 498507045 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 168960 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169024 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 86603112 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169088 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169152 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 87554627 d169 d170
private def d164 : MobiusHarmonicTree := .branch 174157739 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169216 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169280 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 86005847 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169344 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169408 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 81784756 d176 d177
private def d171 : MobiusHarmonicTree := .branch 167790603 d172 d175
private def d163 : MobiusHarmonicTree := .branch 341948342 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169472 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169536 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 86070336 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169600 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169664 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 88823315 d184 d185
private def d179 : MobiusHarmonicTree := .branch 174893651 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169728 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169792 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 82967674 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169856 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169920 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 72434798 d191 d192
private def d186 : MobiusHarmonicTree := .branch 155402472 d187 d190
private def d178 : MobiusHarmonicTree := .branch 330296123 d179 d186
private def d162 : MobiusHarmonicTree := .branch 672244465 d163 d178
private def d130 : MobiusHarmonicTree := .branch 1170751510 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 169984 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170048 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 72214970 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170112 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170176 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 75198526 d201 d202
private def d196 : MobiusHarmonicTree := .branch 147413496 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170240 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170304 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 69834632 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170368 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170432 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 64371760 d208 d209
private def d203 : MobiusHarmonicTree := .branch 134206392 d204 d207
private def d195 : MobiusHarmonicTree := .branch 281619888 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170496 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170560 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 66833315 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170624 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170688 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 69436526 d216 d217
private def d211 : MobiusHarmonicTree := .branch 136269841 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170752 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170816 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 71791319 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170880 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 170944 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 74890126 d223 d224
private def d218 : MobiusHarmonicTree := .branch 146681445 d219 d222
private def d210 : MobiusHarmonicTree := .branch 282951286 d211 d218
private def d194 : MobiusHarmonicTree := .branch 564571174 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171008 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171072 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 73034111 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171136 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171200 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 76203358 d232 d233
private def d227 : MobiusHarmonicTree := .branch 149237469 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171264 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171328 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 82087758 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171392 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171456 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 85206128 d239 d240
private def d234 : MobiusHarmonicTree := .branch 167293886 d235 d238
private def d226 : MobiusHarmonicTree := .branch 316531355 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171520 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171584 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 78970588 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171648 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171712 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 68732624 d247 d248
private def d242 : MobiusHarmonicTree := .branch 147703212 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171776 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171840 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 65980035 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171904 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock020 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 171968 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 62418934 d254 d255
private def d249 : MobiusHarmonicTree := .branch 128398969 d250 d253
private def d241 : MobiusHarmonicTree := .branch 276102181 d242 d249
private def d225 : MobiusHarmonicTree := .branch 592633536 d226 d241
private def d193 : MobiusHarmonicTree := .branch 1157204710 d194 d225
private def d129 : MobiusHarmonicTree := .branch 2327956220 d130 d193
private def d1 : MobiusHarmonicTree := .branch 3155136497 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172032 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172096 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 58444948 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172160 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172224 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 61605747 d266 d267
private def d261 : MobiusHarmonicTree := .branch 120050695 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172288 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172352 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 62564140 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172416 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172480 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 62494368 d273 d274
private def d268 : MobiusHarmonicTree := .branch 125058508 d269 d272
private def d260 : MobiusHarmonicTree := .branch 245109203 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172544 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172608 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 59980159 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172672 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172736 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 64039758 d281 d282
private def d276 : MobiusHarmonicTree := .branch 124019917 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172800 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172864 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 63790752 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172928 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 172992 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 60187903 d288 d289
private def d283 : MobiusHarmonicTree := .branch 123978655 d284 d287
private def d275 : MobiusHarmonicTree := .branch 247998572 d276 d283
private def d259 : MobiusHarmonicTree := .branch 493107775 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173056 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173120 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 64007725 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173184 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173248 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 61415073 d297 d298
private def d292 : MobiusHarmonicTree := .branch 125422798 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173312 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173376 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 61080423 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173440 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173504 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 69509039 d304 d305
private def d299 : MobiusHarmonicTree := .branch 130589462 d300 d303
private def d291 : MobiusHarmonicTree := .branch 256012260 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173568 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173632 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 66324541 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173696 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173760 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 66396332 d312 d313
private def d307 : MobiusHarmonicTree := .branch 132720873 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173824 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173888 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 63484043 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 173952 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174016 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 60776386 d319 d320
private def d314 : MobiusHarmonicTree := .branch 124260429 d315 d318
private def d306 : MobiusHarmonicTree := .branch 256981302 d307 d314
private def d290 : MobiusHarmonicTree := .branch 512993562 d291 d306
private def d258 : MobiusHarmonicTree := .branch 1006101337 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174080 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174144 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 52411552 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174208 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174272 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 52659101 d329 d330
private def d324 : MobiusHarmonicTree := .branch 105070653 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174336 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174400 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 54959795 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174464 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174528 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 57165936 d336 d337
private def d331 : MobiusHarmonicTree := .branch 112125731 d332 d335
private def d323 : MobiusHarmonicTree := .branch 217196384 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174592 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174656 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 60467538 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174720 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174784 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 59279079 d344 d345
private def d339 : MobiusHarmonicTree := .branch 119746617 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174848 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174912 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 57835707 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 174976 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175040 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 54798896 d351 d352
private def d346 : MobiusHarmonicTree := .branch 112634603 d347 d350
private def d338 : MobiusHarmonicTree := .branch 232381220 d339 d346
private def d322 : MobiusHarmonicTree := .branch 449577604 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175104 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175168 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 63413099 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175232 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175296 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 72254236 d360 d361
private def d355 : MobiusHarmonicTree := .branch 135667335 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175360 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175424 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 76438286 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175488 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175552 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 80209385 d367 d368
private def d362 : MobiusHarmonicTree := .branch 156647671 d363 d366
private def d354 : MobiusHarmonicTree := .branch 292315006 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175616 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175680 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 82776716 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175744 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175808 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 77254630 d375 d376
private def d370 : MobiusHarmonicTree := .branch 160031346 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175872 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 175936 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 75340680 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176000 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176064 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 72263861 d382 d383
private def d377 : MobiusHarmonicTree := .branch 147604541 d378 d381
private def d369 : MobiusHarmonicTree := .branch 307635887 d370 d377
private def d353 : MobiusHarmonicTree := .branch 599950893 d354 d369
private def d321 : MobiusHarmonicTree := .branch 1049528497 d322 d353
private def d257 : MobiusHarmonicTree := .branch 2055629834 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176128 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176192 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 66246957 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176256 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176320 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 55133892 d393 d394
private def d388 : MobiusHarmonicTree := .branch 121380849 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176384 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176448 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 45442056 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176512 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176576 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 33408607 d400 d401
private def d395 : MobiusHarmonicTree := .branch 78850663 d396 d399
private def d387 : MobiusHarmonicTree := .branch 200231512 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176640 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176704 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 32342144 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176768 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176832 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 34552839 d408 d409
private def d403 : MobiusHarmonicTree := .branch 66894983 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176896 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 176960 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 28820359 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177024 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177088 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 34756456 d415 d416
private def d410 : MobiusHarmonicTree := .branch 63576815 d411 d414
private def d402 : MobiusHarmonicTree := .branch 130471798 d403 d410
private def d386 : MobiusHarmonicTree := .branch 330703310 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177152 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177216 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 37197397 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177280 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177344 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 40920684 d424 d425
private def d419 : MobiusHarmonicTree := .branch 78118081 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177408 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177472 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 35566392 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177536 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177600 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 40866625 d431 d432
private def d426 : MobiusHarmonicTree := .branch 76433017 d427 d430
private def d418 : MobiusHarmonicTree := .branch 154551098 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177664 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177728 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 50363318 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177792 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177856 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 53801747 d439 d440
private def d434 : MobiusHarmonicTree := .branch 104165065 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177920 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 177984 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 50684882 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178048 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178112 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 57025106 d446 d447
private def d441 : MobiusHarmonicTree := .branch 107709988 d442 d445
private def d433 : MobiusHarmonicTree := .branch 211875053 d434 d441
private def d417 : MobiusHarmonicTree := .branch 366426151 d418 d433
private def d385 : MobiusHarmonicTree := .branch 697129461 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178176 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178240 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 65742687 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178304 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178368 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 63801251 d456 d457
private def d451 : MobiusHarmonicTree := .branch 129543938 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178432 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178496 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 62511460 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178560 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178624 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 57993548 d463 d464
private def d458 : MobiusHarmonicTree := .branch 120505008 d459 d462
private def d450 : MobiusHarmonicTree := .branch 250048946 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178688 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178752 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 58902853 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178816 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178880 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 54679444 d471 d472
private def d466 : MobiusHarmonicTree := .branch 113582297 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 178944 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179008 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 55963713 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179072 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179136 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 54428218 d478 d479
private def d473 : MobiusHarmonicTree := .branch 110391931 d474 d477
private def d465 : MobiusHarmonicTree := .branch 223974228 d466 d473
private def d449 : MobiusHarmonicTree := .branch 474023174 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179200 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179264 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 55605749 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179328 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179392 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 56653116 d487 d488
private def d482 : MobiusHarmonicTree := .branch 112258865 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179456 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179520 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 50668957 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179584 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179648 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 42277523 d494 d495
private def d489 : MobiusHarmonicTree := .branch 92946480 d490 d493
private def d481 : MobiusHarmonicTree := .branch 205205345 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179712 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179776 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 35121882 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179840 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179904 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 29249346 d502 d503
private def d497 : MobiusHarmonicTree := .branch 64371228 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 179968 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180032 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 30166561 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180096 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock021 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 180160 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 37410302 d509 d510
private def d504 : MobiusHarmonicTree := .branch 67576863 d505 d508
private def d496 : MobiusHarmonicTree := .branch 131948091 d497 d504
private def d480 : MobiusHarmonicTree := .branch 337153436 d481 d496
private def d448 : MobiusHarmonicTree := .branch 811176610 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1508306071 d385 d448
private def d256 : MobiusHarmonicTree := .branch 3563935905 d257 d384
private def d0 : MobiusHarmonicTree := .branch 6719072402 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 163840 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 163840 6719072402 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 163840 3155136497 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 163840 827180277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 163840 367871827 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 163840 91834087 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 163840 44565553 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 163840 20218873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 163840 5435449 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 163968 14783424 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 164096 24346680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 164096 14583395 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 164224 9763285 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 164352 47268534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 164352 19867639 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 164352 8600455 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 164480 11267184 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 164608 27400895 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 164608 13165606 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 164736 14235289 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 164864 276037740 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 164864 133941536 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 164864 52961412 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 164864 20996589 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 164992 31964823 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 165120 80980124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 165120 39149900 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 165248 41830224 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 165376 142096204 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 165376 71513441 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 165376 40667404 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 165504 30846037 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 165632 70582763 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 165632 33199540 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 165760 37383223 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 165888 459308450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 165888 243950762 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 165888 133793243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 165888 72739370 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 165888 35034344 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 166016 37705026 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 166144 61053873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 166144 33687093 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 166272 27366780 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 166400 110157519 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 166400 57832461 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 166400 26479617 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 166528 31352844 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 166656 52325058 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 166656 25761577 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 166784 26563481 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 166912 215357688 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 166912 101989108 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 166912 46292446 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 166912 28213961 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 167040 18078485 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 167168 55696662 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 167168 26759108 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 167296 28937554 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 167424 113368580 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 167424 53530679 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 167424 26778060 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 167552 26752619 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 167680 59837901 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 167680 24531421 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 167808 35306480 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 167936 2327956220 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 167936 1170751510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 167936 498507045 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 167936 218415367 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 167936 103330821 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 167936 46588754 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 168064 56742067 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 168192 115084546 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 168192 57894152 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 168320 57190394 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 168448 280091678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 168448 126278806 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 168448 60061369 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 168576 66217437 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 168704 153812872 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 168704 73129828 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 168832 80683044 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 168960 672244465 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 168960 341948342 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 168960 174157739 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 168960 86603112 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 169088 87554627 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 169216 167790603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 169216 86005847 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 169344 81784756 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 169472 330296123 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 169472 174893651 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 169472 86070336 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 169600 88823315 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 169728 155402472 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 169728 82967674 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 169856 72434798 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 169984 1157204710 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 169984 564571174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 169984 281619888 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 169984 147413496 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 169984 72214970 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 170112 75198526 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 170240 134206392 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 170240 69834632 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 170368 64371760 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 170496 282951286 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 170496 136269841 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 170496 66833315 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 170624 69436526 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 170752 146681445 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 170752 71791319 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 170880 74890126 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 171008 592633536 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 171008 316531355 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 171008 149237469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 171008 73034111 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 171136 76203358 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 171264 167293886 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 171264 82087758 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 171392 85206128 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 171520 276102181 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 171520 147703212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 171520 78970588 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 171648 68732624 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 171776 128398969 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 171776 65980035 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 171904 62418934 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 172032 3563935905 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 172032 2055629834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 172032 1006101337 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 172032 493107775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 172032 245109203 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 172032 120050695 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 172032 58444948 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 172160 61605747 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 172288 125058508 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 172288 62564140 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 172416 62494368 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 172544 247998572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 172544 124019917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 172544 59980159 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 172672 64039758 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 172800 123978655 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 172800 63790752 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 172928 60187903 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 173056 512993562 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 173056 256012260 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 173056 125422798 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 173056 64007725 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 173184 61415073 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 173312 130589462 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 173312 61080423 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 173440 69509039 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 173568 256981302 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 173568 132720873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 173568 66324541 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 173696 66396332 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 173824 124260429 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 173824 63484043 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 173952 60776386 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 174080 1049528497 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 174080 449577604 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 174080 217196384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 174080 105070653 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 174080 52411552 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 174208 52659101 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 174336 112125731 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 174336 54959795 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 174464 57165936 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 174592 232381220 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 174592 119746617 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 174592 60467538 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 174720 59279079 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 174848 112634603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 174848 57835707 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 174976 54798896 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 175104 599950893 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 175104 292315006 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 175104 135667335 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 175104 63413099 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 175232 72254236 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 175360 156647671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 175360 76438286 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 175488 80209385 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 175616 307635887 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 175616 160031346 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 175616 82776716 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 175744 77254630 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 175872 147604541 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 175872 75340680 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 176000 72263861 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 176128 1508306071 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 176128 697129461 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 176128 330703310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 176128 200231512 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 176128 121380849 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 176128 66246957 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 176256 55133892 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 176384 78850663 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 176384 45442056 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 176512 33408607 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 176640 130471798 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 176640 66894983 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 176640 32342144 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 176768 34552839 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 176896 63576815 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 176896 28820359 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 177024 34756456 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 177152 366426151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 177152 154551098 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 177152 78118081 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 177152 37197397 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 177280 40920684 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 177408 76433017 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 177408 35566392 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 177536 40866625 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 177664 211875053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 177664 104165065 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 177664 50363318 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 177792 53801747 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 177920 107709988 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 177920 50684882 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 178048 57025106 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 178176 811176610 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 178176 474023174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 178176 250048946 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 178176 129543938 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 178176 65742687 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 178304 63801251 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 178432 120505008 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 178432 62511460 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 178560 57993548 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 178688 223974228 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 178688 113582297 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 178688 58902853 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 178816 54679444 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 178944 110391931 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 178944 55963713 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 179072 54428218 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 179200 337153436 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 179200 205205345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 179200 112258865 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 179200 55605749 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 179328 56653116 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 179456 92946480 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 179456 50668957 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 179584 42277523 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 179712 131948091 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 179712 64371228 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 179712 35121882 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 179840 29249346 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 179968 67576863 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 179968 30166561 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 180096 37410302 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 163840 (MobiusHarmonicTree.branch 6719072402 mobiusHarmonicBlock020 mobiusHarmonicBlock021) = true := Helfgott.combined

#print axioms solution
