-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair016_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:50:31.307062+00:00
-- url     : https://prove2.me/submissions/fa6dc3e7-c230-442a-a427-2ca9f8a6020a

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262144 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262208 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 12669344 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262272 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262336 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 12167987 d11 d12
private def d6 : MobiusHarmonicTree := .branch 24837331 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262400 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262464 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 6336384 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262528 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262592 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 4726030 d18 d19
private def d13 : MobiusHarmonicTree := .branch 11062414 d14 d17
private def d5 : MobiusHarmonicTree := .branch 35899745 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262656 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262720 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 1446479 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262784 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262848 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 6288515 d26 d27
private def d21 : MobiusHarmonicTree := .branch 7734994 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262912 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262976 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 16700885 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263040 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263104 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 18472174 d33 d34
private def d28 : MobiusHarmonicTree := .branch 35173059 d29 d32
private def d20 : MobiusHarmonicTree := .branch 42908053 d21 d28
private def d4 : MobiusHarmonicTree := .branch 78807798 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263168 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263232 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 15712494 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263296 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263360 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 15890924 d42 d43
private def d37 : MobiusHarmonicTree := .branch 31603418 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263424 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263488 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 15534006 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263552 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263616 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 15610045 d49 d50
private def d44 : MobiusHarmonicTree := .branch 31144051 d45 d48
private def d36 : MobiusHarmonicTree := .branch 62747469 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263680 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263744 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 14900904 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263808 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263872 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 14882265 d57 d58
private def d52 : MobiusHarmonicTree := .branch 29783169 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 263936 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264000 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 9651653 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264064 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264128 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 9121022 d64 d65
private def d59 : MobiusHarmonicTree := .branch 18772675 d60 d63
private def d51 : MobiusHarmonicTree := .branch 48555844 d52 d59
private def d35 : MobiusHarmonicTree := .branch 111303313 d36 d51
private def d3 : MobiusHarmonicTree := .branch 190111111 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264192 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264256 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 7148456 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264320 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264384 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 5809915 d74 d75
private def d69 : MobiusHarmonicTree := .branch 12958371 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264448 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264512 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 6460882 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264576 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264640 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 5800344 d81 d82
private def d76 : MobiusHarmonicTree := .branch 12261226 d77 d80
private def d68 : MobiusHarmonicTree := .branch 25219597 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264704 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264768 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 7187783 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264832 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264896 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 3106989 d89 d90
private def d84 : MobiusHarmonicTree := .branch 10294772 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 264960 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265024 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 2052440 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265088 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265152 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 3092967 d96 d97
private def d91 : MobiusHarmonicTree := .branch 5145407 d92 d95
private def d83 : MobiusHarmonicTree := .branch 15440179 d84 d91
private def d67 : MobiusHarmonicTree := .branch 40659776 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265216 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265280 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 2491830 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265344 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265408 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 727236 d105 d106
private def d100 : MobiusHarmonicTree := .branch 3219066 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265472 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265536 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 2142919 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265600 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265664 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 1961110 d112 d113
private def d107 : MobiusHarmonicTree := .branch 4104029 d108 d111
private def d99 : MobiusHarmonicTree := .branch 7323095 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265728 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265792 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 2881956 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265856 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265920 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 3685303 d120 d121
private def d115 : MobiusHarmonicTree := .branch 6567259 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 265984 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266048 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 8017732 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266112 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266176 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 935545 d127 d128
private def d122 : MobiusHarmonicTree := .branch 8953277 d123 d126
private def d114 : MobiusHarmonicTree := .branch 15520536 d115 d122
private def d98 : MobiusHarmonicTree := .branch 22843631 d99 d114
private def d66 : MobiusHarmonicTree := .branch 63503407 d67 d98
private def d2 : MobiusHarmonicTree := .branch 253614518 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266240 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266304 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 1513372 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266368 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266432 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 1227422 d138 d139
private def d133 : MobiusHarmonicTree := .branch 2740794 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266496 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266560 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 4306413 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266624 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266688 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 7672196 d145 d146
private def d140 : MobiusHarmonicTree := .branch 11978609 d141 d144
private def d132 : MobiusHarmonicTree := .branch 14719403 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266752 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266816 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 5513237 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266880 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 266944 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 3866281 d153 d154
private def d148 : MobiusHarmonicTree := .branch 9379518 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267008 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267072 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 2482444 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267136 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267200 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 1882562 d160 d161
private def d155 : MobiusHarmonicTree := .branch 4365006 d156 d159
private def d147 : MobiusHarmonicTree := .branch 13744524 d148 d155
private def d131 : MobiusHarmonicTree := .branch 28463927 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267264 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267328 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 953910 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267392 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267456 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 1854386 d169 d170
private def d164 : MobiusHarmonicTree := .branch 2808296 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267520 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267584 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 9992944 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267648 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267712 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 15632356 d176 d177
private def d171 : MobiusHarmonicTree := .branch 25625300 d172 d175
private def d163 : MobiusHarmonicTree := .branch 28433596 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267776 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267840 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 23950510 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267904 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 267968 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 28776188 d184 d185
private def d179 : MobiusHarmonicTree := .branch 52726698 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268032 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268096 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 26412492 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268160 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268224 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 23357326 d191 d192
private def d186 : MobiusHarmonicTree := .branch 49769818 d187 d190
private def d178 : MobiusHarmonicTree := .branch 102496516 d179 d186
private def d162 : MobiusHarmonicTree := .branch 130930112 d163 d178
private def d130 : MobiusHarmonicTree := .branch 159394039 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268288 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268352 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 20782879 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268416 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268480 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 16556342 d201 d202
private def d196 : MobiusHarmonicTree := .branch 37339221 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268544 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268608 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 11262027 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268672 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268736 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 7650620 d208 d209
private def d203 : MobiusHarmonicTree := .branch 18912647 d204 d207
private def d195 : MobiusHarmonicTree := .branch 56251868 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268800 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268864 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 12641933 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268928 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 268992 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 18119684 d216 d217
private def d211 : MobiusHarmonicTree := .branch 30761617 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269056 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269120 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 19619489 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269184 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269248 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 21998316 d223 d224
private def d218 : MobiusHarmonicTree := .branch 41617805 d219 d222
private def d210 : MobiusHarmonicTree := .branch 72379422 d211 d218
private def d194 : MobiusHarmonicTree := .branch 128631290 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269312 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269376 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 23528465 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269440 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269504 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 23205674 d232 d233
private def d227 : MobiusHarmonicTree := .branch 46734139 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269568 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269632 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 27730333 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269696 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269760 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 28788437 d239 d240
private def d234 : MobiusHarmonicTree := .branch 56518770 d235 d238
private def d226 : MobiusHarmonicTree := .branch 103252909 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269824 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269888 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 27752500 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 269952 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270016 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 22861995 d247 d248
private def d242 : MobiusHarmonicTree := .branch 50614495 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270080 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270144 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 25460218 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270208 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock032 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270272 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 24964094 d254 d255
private def d249 : MobiusHarmonicTree := .branch 50424312 d250 d253
private def d241 : MobiusHarmonicTree := .branch 101038807 d242 d249
private def d225 : MobiusHarmonicTree := .branch 204291716 d226 d241
private def d193 : MobiusHarmonicTree := .branch 332923006 d194 d225
private def d129 : MobiusHarmonicTree := .branch 492317045 d130 d193
private def d1 : MobiusHarmonicTree := .branch 745931563 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270336 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270400 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 24571117 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270464 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270528 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 26296956 d266 d267
private def d261 : MobiusHarmonicTree := .branch 50868073 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270592 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270656 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 27049198 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270720 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270784 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 29883406 d273 d274
private def d268 : MobiusHarmonicTree := .branch 56932604 d269 d272
private def d260 : MobiusHarmonicTree := .branch 107800677 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270848 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270912 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 27459388 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 270976 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271040 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 28386754 d281 d282
private def d276 : MobiusHarmonicTree := .branch 55846142 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271104 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271168 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 30512863 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271232 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271296 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 26790108 d288 d289
private def d283 : MobiusHarmonicTree := .branch 57302971 d284 d287
private def d275 : MobiusHarmonicTree := .branch 113149113 d276 d283
private def d259 : MobiusHarmonicTree := .branch 220949790 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271360 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271424 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 24239068 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271488 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271552 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 22084342 d297 d298
private def d292 : MobiusHarmonicTree := .branch 46323410 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271616 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271680 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 20487500 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271744 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271808 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 19513932 d304 d305
private def d299 : MobiusHarmonicTree := .branch 40001432 d300 d303
private def d291 : MobiusHarmonicTree := .branch 86324842 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271872 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 271936 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 19313410 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272000 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272064 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 21351870 d312 d313
private def d307 : MobiusHarmonicTree := .branch 40665280 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272128 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272192 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 18262909 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272256 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272320 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 21893245 d319 d320
private def d314 : MobiusHarmonicTree := .branch 40156154 d315 d318
private def d306 : MobiusHarmonicTree := .branch 80821434 d307 d314
private def d290 : MobiusHarmonicTree := .branch 167146276 d291 d306
private def d258 : MobiusHarmonicTree := .branch 388096066 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272384 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272448 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 24342509 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272512 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272576 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 19213019 d329 d330
private def d324 : MobiusHarmonicTree := .branch 43555528 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272640 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272704 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 20696554 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272768 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272832 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 17769379 d336 d337
private def d331 : MobiusHarmonicTree := .branch 38465933 d332 d335
private def d323 : MobiusHarmonicTree := .branch 82021461 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272896 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 272960 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 17200443 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273024 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273088 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 18712007 d344 d345
private def d339 : MobiusHarmonicTree := .branch 35912450 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273152 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273216 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 17564978 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273280 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273344 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 18778545 d351 d352
private def d346 : MobiusHarmonicTree := .branch 36343523 d347 d350
private def d338 : MobiusHarmonicTree := .branch 72255973 d339 d346
private def d322 : MobiusHarmonicTree := .branch 154277434 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273408 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273472 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 10725391 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273536 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273600 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 9031650 d360 d361
private def d355 : MobiusHarmonicTree := .branch 19757041 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273664 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273728 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 6126842 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273792 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273856 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 3881886 d367 d368
private def d362 : MobiusHarmonicTree := .branch 10008728 d363 d366
private def d354 : MobiusHarmonicTree := .branch 29765769 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273920 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 273984 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 1722661 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274048 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274112 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 7321871 d375 d376
private def d370 : MobiusHarmonicTree := .branch 9044532 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274176 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274240 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 4463454 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274304 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274368 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 2252425 d382 d383
private def d377 : MobiusHarmonicTree := .branch 6715879 d378 d381
private def d369 : MobiusHarmonicTree := .branch 15760411 d370 d377
private def d353 : MobiusHarmonicTree := .branch 45526180 d354 d369
private def d321 : MobiusHarmonicTree := .branch 199803614 d322 d353
private def d257 : MobiusHarmonicTree := .branch 587899680 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274432 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274496 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 3034687 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274560 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274624 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 3914494 d393 d394
private def d388 : MobiusHarmonicTree := .branch 6949181 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274688 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274752 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 7493802 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274816 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274880 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 11346786 d400 d401
private def d395 : MobiusHarmonicTree := .branch 18840588 d396 d399
private def d387 : MobiusHarmonicTree := .branch 25789769 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 274944 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275008 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 8632701 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275072 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275136 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 3922001 d408 d409
private def d403 : MobiusHarmonicTree := .branch 12554702 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275200 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275264 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 2401363 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275328 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275392 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 1383549 d415 d416
private def d410 : MobiusHarmonicTree := .branch 3784912 d411 d414
private def d402 : MobiusHarmonicTree := .branch 16339614 d403 d410
private def d386 : MobiusHarmonicTree := .branch 42129383 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275456 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275520 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 2511703 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275584 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275648 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 1741520 d424 d425
private def d419 : MobiusHarmonicTree := .branch 4253223 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275712 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275776 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 2705021 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275840 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275904 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 1286797 d431 d432
private def d426 : MobiusHarmonicTree := .branch 3991818 d427 d430
private def d418 : MobiusHarmonicTree := .branch 8245041 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 275968 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276032 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 6046210 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276096 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276160 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 6731707 d439 d440
private def d434 : MobiusHarmonicTree := .branch 12777917 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276224 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276288 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 3717166 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276352 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276416 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 7000253 d446 d447
private def d441 : MobiusHarmonicTree := .branch 10717419 d442 d445
private def d433 : MobiusHarmonicTree := .branch 23495336 d434 d441
private def d417 : MobiusHarmonicTree := .branch 31740377 d418 d433
private def d385 : MobiusHarmonicTree := .branch 73869760 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276480 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276544 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 10208231 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276608 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276672 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 5360534 d456 d457
private def d451 : MobiusHarmonicTree := .branch 15568765 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276736 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276800 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 4624235 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276864 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276928 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 7796325 d463 d464
private def d458 : MobiusHarmonicTree := .branch 12420560 d459 d462
private def d450 : MobiusHarmonicTree := .branch 27989325 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 276992 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277056 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 7507592 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277120 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277184 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 2991035 d471 d472
private def d466 : MobiusHarmonicTree := .branch 10498627 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277248 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277312 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 1298289 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277376 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277440 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 1052459 d478 d479
private def d473 : MobiusHarmonicTree := .branch 2350748 d474 d477
private def d465 : MobiusHarmonicTree := .branch 12849375 d466 d473
private def d449 : MobiusHarmonicTree := .branch 40838700 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277504 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277568 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 2622795 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277632 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277696 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 3802853 d487 d488
private def d482 : MobiusHarmonicTree := .branch 6425648 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277760 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277824 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 4970831 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277888 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 277952 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 3140926 d494 d495
private def d489 : MobiusHarmonicTree := .branch 8111757 d490 d493
private def d481 : MobiusHarmonicTree := .branch 14537405 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278016 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278080 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 4861704 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278144 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278208 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 6017169 d502 d503
private def d497 : MobiusHarmonicTree := .branch 10878873 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278272 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278336 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 4390679 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278400 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock033 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 278464 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 1551391 d509 d510
private def d504 : MobiusHarmonicTree := .branch 5942070 d505 d508
private def d496 : MobiusHarmonicTree := .branch 16820943 d497 d504
private def d480 : MobiusHarmonicTree := .branch 31358348 d481 d496
private def d448 : MobiusHarmonicTree := .branch 72197048 d449 d480
private def d384 : MobiusHarmonicTree := .branch 146066808 d385 d448
private def d256 : MobiusHarmonicTree := .branch 733966488 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1479898051 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 262144 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 262144 1479898051 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 262144 745931563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 262144 253614518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 262144 190111111 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 262144 78807798 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 262144 35899745 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 262144 24837331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 262144 12669344 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 262272 12167987 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 262400 11062414 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 262400 6336384 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 262528 4726030 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 262656 42908053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 262656 7734994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 262656 1446479 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 262784 6288515 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 262912 35173059 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 262912 16700885 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 263040 18472174 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 263168 111303313 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 263168 62747469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 263168 31603418 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 263168 15712494 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 263296 15890924 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 263424 31144051 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 263424 15534006 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 263552 15610045 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 263680 48555844 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 263680 29783169 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 263680 14900904 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 263808 14882265 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 263936 18772675 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 263936 9651653 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 264064 9121022 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 264192 63503407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 264192 40659776 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 264192 25219597 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 264192 12958371 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 264192 7148456 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 264320 5809915 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 264448 12261226 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 264448 6460882 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 264576 5800344 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 264704 15440179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 264704 10294772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 264704 7187783 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 264832 3106989 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 264960 5145407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 264960 2052440 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 265088 3092967 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 265216 22843631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 265216 7323095 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 265216 3219066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 265216 2491830 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 265344 727236 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 265472 4104029 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 265472 2142919 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 265600 1961110 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 265728 15520536 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 265728 6567259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 265728 2881956 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 265856 3685303 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 265984 8953277 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 265984 8017732 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 266112 935545 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 266240 492317045 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 266240 159394039 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 266240 28463927 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 266240 14719403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 266240 2740794 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 266240 1513372 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 266368 1227422 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 266496 11978609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 266496 4306413 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 266624 7672196 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 266752 13744524 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 266752 9379518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 266752 5513237 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 266880 3866281 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 267008 4365006 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 267008 2482444 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 267136 1882562 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 267264 130930112 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 267264 28433596 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 267264 2808296 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 267264 953910 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 267392 1854386 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 267520 25625300 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 267520 9992944 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 267648 15632356 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 267776 102496516 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 267776 52726698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 267776 23950510 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 267904 28776188 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 268032 49769818 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 268032 26412492 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 268160 23357326 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 268288 332923006 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 268288 128631290 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 268288 56251868 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 268288 37339221 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 268288 20782879 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 268416 16556342 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 268544 18912647 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 268544 11262027 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 268672 7650620 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 268800 72379422 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 268800 30761617 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 268800 12641933 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 268928 18119684 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 269056 41617805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 269056 19619489 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 269184 21998316 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 269312 204291716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 269312 103252909 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 269312 46734139 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 269312 23528465 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 269440 23205674 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 269568 56518770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 269568 27730333 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 269696 28788437 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 269824 101038807 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 269824 50614495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 269824 27752500 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 269952 22861995 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 270080 50424312 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 270080 25460218 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 270208 24964094 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 270336 733966488 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 270336 587899680 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 270336 388096066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 270336 220949790 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 270336 107800677 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 270336 50868073 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 270336 24571117 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 270464 26296956 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 270592 56932604 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 270592 27049198 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 270720 29883406 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 270848 113149113 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 270848 55846142 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 270848 27459388 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 270976 28386754 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 271104 57302971 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 271104 30512863 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 271232 26790108 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 271360 167146276 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 271360 86324842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 271360 46323410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 271360 24239068 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 271488 22084342 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 271616 40001432 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 271616 20487500 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 271744 19513932 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 271872 80821434 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 271872 40665280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 271872 19313410 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 272000 21351870 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 272128 40156154 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 272128 18262909 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 272256 21893245 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 272384 199803614 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 272384 154277434 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 272384 82021461 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 272384 43555528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 272384 24342509 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 272512 19213019 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 272640 38465933 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 272640 20696554 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 272768 17769379 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 272896 72255973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 272896 35912450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 272896 17200443 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 273024 18712007 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 273152 36343523 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 273152 17564978 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 273280 18778545 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 273408 45526180 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 273408 29765769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 273408 19757041 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 273408 10725391 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 273536 9031650 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 273664 10008728 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 273664 6126842 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 273792 3881886 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 273920 15760411 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 273920 9044532 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 273920 1722661 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 274048 7321871 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 274176 6715879 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 274176 4463454 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 274304 2252425 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 274432 146066808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 274432 73869760 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 274432 42129383 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 274432 25789769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 274432 6949181 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 274432 3034687 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 274560 3914494 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 274688 18840588 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 274688 7493802 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 274816 11346786 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 274944 16339614 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 274944 12554702 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 274944 8632701 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 275072 3922001 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 275200 3784912 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 275200 2401363 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 275328 1383549 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 275456 31740377 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 275456 8245041 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 275456 4253223 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 275456 2511703 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 275584 1741520 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 275712 3991818 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 275712 2705021 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 275840 1286797 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 275968 23495336 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 275968 12777917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 275968 6046210 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 276096 6731707 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 276224 10717419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 276224 3717166 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 276352 7000253 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 276480 72197048 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 276480 40838700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 276480 27989325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 276480 15568765 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 276480 10208231 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 276608 5360534 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 276736 12420560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 276736 4624235 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 276864 7796325 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 276992 12849375 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 276992 10498627 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 276992 7507592 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 277120 2991035 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 277248 2350748 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 277248 1298289 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 277376 1052459 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 277504 31358348 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 277504 14537405 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 277504 6425648 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 277504 2622795 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 277632 3802853 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 277760 8111757 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 277760 4970831 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 277888 3140926 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 278016 16820943 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 278016 10878873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 278016 4861704 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 278144 6017169 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 278272 5942070 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 278272 4390679 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 278400 1551391 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 262144 (MobiusHarmonicTree.branch 1479898051 mobiusHarmonicBlock032 mobiusHarmonicBlock033) = true := Helfgott.combined

#print axioms solution
