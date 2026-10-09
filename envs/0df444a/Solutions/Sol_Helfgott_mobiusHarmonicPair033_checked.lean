-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair033_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:57:34.463805+00:00
-- url     : https://prove2.me/submissions/49f48b31-2b0b-48b5-872c-76de3bc64932

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540672 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540736 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 13296798 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540800 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540864 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 12803708 d11 d12
private def d6 : MobiusHarmonicTree := .branch 26100506 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540928 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 540992 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 9979876 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541056 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541120 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 9524785 d18 d19
private def d13 : MobiusHarmonicTree := .branch 19504661 d14 d17
private def d5 : MobiusHarmonicTree := .branch 45605167 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541184 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541248 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 9309973 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541312 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541376 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 9666199 d26 d27
private def d21 : MobiusHarmonicTree := .branch 18976172 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541440 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541504 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 8051745 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541568 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541632 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 7828243 d33 d34
private def d28 : MobiusHarmonicTree := .branch 15879988 d29 d32
private def d20 : MobiusHarmonicTree := .branch 34856160 d21 d28
private def d4 : MobiusHarmonicTree := .branch 80461327 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541696 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541760 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 11488481 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541824 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541888 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 10504154 d42 d43
private def d37 : MobiusHarmonicTree := .branch 21992635 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 541952 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542016 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 9988761 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542080 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542144 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 9479046 d49 d50
private def d44 : MobiusHarmonicTree := .branch 19467807 d45 d48
private def d36 : MobiusHarmonicTree := .branch 41460442 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542208 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542272 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 12112057 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542336 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542400 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 11513746 d57 d58
private def d52 : MobiusHarmonicTree := .branch 23625803 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542464 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542528 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 10161753 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542592 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542656 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 8825248 d64 d65
private def d59 : MobiusHarmonicTree := .branch 18987001 d60 d63
private def d51 : MobiusHarmonicTree := .branch 42612804 d52 d59
private def d35 : MobiusHarmonicTree := .branch 84073246 d36 d51
private def d3 : MobiusHarmonicTree := .branch 164534573 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542720 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542784 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 8399339 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542848 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542912 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 8690221 d74 d75
private def d69 : MobiusHarmonicTree := .branch 17089560 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 542976 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543040 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 9047299 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543104 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543168 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 10123949 d81 d82
private def d76 : MobiusHarmonicTree := .branch 19171248 d77 d80
private def d68 : MobiusHarmonicTree := .branch 36260808 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543232 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543296 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 11678781 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543360 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543424 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 13902669 d89 d90
private def d84 : MobiusHarmonicTree := .branch 25581450 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543488 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543552 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 13623492 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543616 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543680 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 12704226 d96 d97
private def d91 : MobiusHarmonicTree := .branch 26327718 d92 d95
private def d83 : MobiusHarmonicTree := .branch 51909168 d84 d91
private def d67 : MobiusHarmonicTree := .branch 88169976 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543744 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543808 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 13444108 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543872 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 543936 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 13979691 d105 d106
private def d100 : MobiusHarmonicTree := .branch 27423799 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544000 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544064 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 13641872 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544128 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544192 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 14855092 d112 d113
private def d107 : MobiusHarmonicTree := .branch 28496964 d108 d111
private def d99 : MobiusHarmonicTree := .branch 55920763 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544256 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544320 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 14958266 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544384 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544448 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 11391496 d120 d121
private def d115 : MobiusHarmonicTree := .branch 26349762 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544512 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544576 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 8145881 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544640 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544704 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 5876691 d127 d128
private def d122 : MobiusHarmonicTree := .branch 14022572 d123 d126
private def d114 : MobiusHarmonicTree := .branch 40372334 d115 d122
private def d98 : MobiusHarmonicTree := .branch 96293097 d99 d114
private def d66 : MobiusHarmonicTree := .branch 184463073 d67 d98
private def d2 : MobiusHarmonicTree := .branch 348997646 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544768 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544832 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 4438171 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544896 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 544960 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 4642598 d138 d139
private def d133 : MobiusHarmonicTree := .branch 9080769 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545024 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545088 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 5368002 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545152 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545216 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 5377783 d145 d146
private def d140 : MobiusHarmonicTree := .branch 10745785 d141 d144
private def d132 : MobiusHarmonicTree := .branch 19826554 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545280 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545344 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 2919376 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545408 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545472 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 2944255 d153 d154
private def d148 : MobiusHarmonicTree := .branch 5863631 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545536 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545600 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 3313826 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545664 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545728 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 1187528 d160 d161
private def d155 : MobiusHarmonicTree := .branch 4501354 d156 d159
private def d147 : MobiusHarmonicTree := .branch 10364985 d148 d155
private def d131 : MobiusHarmonicTree := .branch 30191539 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545792 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545856 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 892229 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545920 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 545984 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 1135616 d169 d170
private def d164 : MobiusHarmonicTree := .branch 2027845 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546048 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546112 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 1281844 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546176 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546240 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 1352994 d176 d177
private def d171 : MobiusHarmonicTree := .branch 2634838 d172 d175
private def d163 : MobiusHarmonicTree := .branch 4662683 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546304 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546368 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 728515 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546432 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546496 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 2422759 d184 d185
private def d179 : MobiusHarmonicTree := .branch 3151274 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546560 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546624 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 4566269 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546688 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546752 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 3244725 d191 d192
private def d186 : MobiusHarmonicTree := .branch 7810994 d187 d190
private def d178 : MobiusHarmonicTree := .branch 10962268 d179 d186
private def d162 : MobiusHarmonicTree := .branch 15624951 d163 d178
private def d130 : MobiusHarmonicTree := .branch 45816490 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546816 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546880 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 2241930 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 546944 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547008 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 1159088 d201 d202
private def d196 : MobiusHarmonicTree := .branch 3401018 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547072 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547136 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 2926200 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547200 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547264 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 3417067 d208 d209
private def d203 : MobiusHarmonicTree := .branch 6343267 d204 d207
private def d195 : MobiusHarmonicTree := .branch 9744285 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547328 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547392 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 3251872 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547456 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547520 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 1358949 d216 d217
private def d211 : MobiusHarmonicTree := .branch 4610821 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547584 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547648 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 818100 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547712 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547776 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 768638 d223 d224
private def d218 : MobiusHarmonicTree := .branch 1586738 d219 d222
private def d210 : MobiusHarmonicTree := .branch 6197559 d211 d218
private def d194 : MobiusHarmonicTree := .branch 15941844 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547840 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547904 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 2529671 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 547968 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548032 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 4330045 d232 d233
private def d227 : MobiusHarmonicTree := .branch 6859716 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548096 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548160 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 7247962 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548224 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548288 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 6368993 d239 d240
private def d234 : MobiusHarmonicTree := .branch 13616955 d235 d238
private def d226 : MobiusHarmonicTree := .branch 20476671 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548352 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548416 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 5373771 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548480 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548544 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 2450263 d247 d248
private def d242 : MobiusHarmonicTree := .branch 7824034 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548608 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548672 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 1314142 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548736 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock066 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548800 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 1652716 d254 d255
private def d249 : MobiusHarmonicTree := .branch 2966858 d250 d253
private def d241 : MobiusHarmonicTree := .branch 10790892 d242 d249
private def d225 : MobiusHarmonicTree := .branch 31267563 d226 d241
private def d193 : MobiusHarmonicTree := .branch 47209407 d194 d225
private def d129 : MobiusHarmonicTree := .branch 93025897 d130 d193
private def d1 : MobiusHarmonicTree := .branch 442023543 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548864 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548928 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 3816572 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 548992 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549056 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 5912002 d266 d267
private def d261 : MobiusHarmonicTree := .branch 9728574 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549120 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549184 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 4870930 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549248 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549312 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 4425655 d273 d274
private def d268 : MobiusHarmonicTree := .branch 9296585 d269 d272
private def d260 : MobiusHarmonicTree := .branch 19025159 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549376 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549440 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 3327059 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549504 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549568 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 4887540 d281 d282
private def d276 : MobiusHarmonicTree := .branch 8214599 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549632 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549696 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 6027017 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549760 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549824 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 4590672 d288 d289
private def d283 : MobiusHarmonicTree := .branch 10617689 d284 d287
private def d275 : MobiusHarmonicTree := .branch 18832288 d276 d283
private def d259 : MobiusHarmonicTree := .branch 37857447 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549888 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 549952 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 1116532 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550016 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550080 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 2085218 d297 d298
private def d292 : MobiusHarmonicTree := .branch 3201750 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550144 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550208 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 1099655 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550272 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550336 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 2105970 d304 d305
private def d299 : MobiusHarmonicTree := .branch 3205625 d300 d303
private def d291 : MobiusHarmonicTree := .branch 6407375 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550400 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550464 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 4171087 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550528 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550592 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 4905685 d312 d313
private def d307 : MobiusHarmonicTree := .branch 9076772 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550656 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550720 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 2923518 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550784 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550848 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 1766497 d319 d320
private def d314 : MobiusHarmonicTree := .branch 4690015 d315 d318
private def d306 : MobiusHarmonicTree := .branch 13766787 d307 d314
private def d290 : MobiusHarmonicTree := .branch 20174162 d291 d306
private def d258 : MobiusHarmonicTree := .branch 58031609 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550912 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 550976 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 1366711 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551040 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551104 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 1076126 d329 d330
private def d324 : MobiusHarmonicTree := .branch 2442837 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551168 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551232 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 1779662 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551296 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551360 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 941361 d336 d337
private def d331 : MobiusHarmonicTree := .branch 2721023 d332 d335
private def d323 : MobiusHarmonicTree := .branch 5163860 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551424 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551488 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 3457929 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551552 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551616 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 2034103 d344 d345
private def d339 : MobiusHarmonicTree := .branch 5492032 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551680 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551744 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 1584137 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551808 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551872 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 1302935 d351 d352
private def d346 : MobiusHarmonicTree := .branch 2887072 d347 d350
private def d338 : MobiusHarmonicTree := .branch 8379104 d339 d346
private def d322 : MobiusHarmonicTree := .branch 13542964 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 551936 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552000 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 1235517 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552064 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552128 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 1798546 d360 d361
private def d355 : MobiusHarmonicTree := .branch 3034063 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552192 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552256 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 3273928 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552320 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552384 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 4381011 d367 d368
private def d362 : MobiusHarmonicTree := .branch 7654939 d363 d366
private def d354 : MobiusHarmonicTree := .branch 10689002 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552448 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552512 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 5399032 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552576 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552640 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 4943604 d375 d376
private def d370 : MobiusHarmonicTree := .branch 10342636 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552704 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552768 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 5298868 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552832 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552896 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 5984858 d382 d383
private def d377 : MobiusHarmonicTree := .branch 11283726 d378 d381
private def d369 : MobiusHarmonicTree := .branch 21626362 d370 d377
private def d353 : MobiusHarmonicTree := .branch 32315364 d354 d369
private def d321 : MobiusHarmonicTree := .branch 45858328 d322 d353
private def d257 : MobiusHarmonicTree := .branch 103889937 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 552960 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553024 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 10207557 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553088 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553152 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 7209712 d393 d394
private def d388 : MobiusHarmonicTree := .branch 17417269 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553216 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553280 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 5149399 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553344 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553408 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 3767616 d400 d401
private def d395 : MobiusHarmonicTree := .branch 8917015 d396 d399
private def d387 : MobiusHarmonicTree := .branch 26334284 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553472 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553536 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 3752317 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553600 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553664 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 2879021 d408 d409
private def d403 : MobiusHarmonicTree := .branch 6631338 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553728 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553792 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 2425157 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553856 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553920 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 993041 d415 d416
private def d410 : MobiusHarmonicTree := .branch 3418198 d411 d414
private def d402 : MobiusHarmonicTree := .branch 10049536 d403 d410
private def d386 : MobiusHarmonicTree := .branch 36383820 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 553984 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554048 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 1084787 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554112 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554176 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 1588037 d424 d425
private def d419 : MobiusHarmonicTree := .branch 2672824 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554240 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554304 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 611628 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554368 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554432 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 533925 d431 d432
private def d426 : MobiusHarmonicTree := .branch 1145553 d427 d430
private def d418 : MobiusHarmonicTree := .branch 3818377 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554496 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554560 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 3784993 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554624 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554688 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 5826782 d439 d440
private def d434 : MobiusHarmonicTree := .branch 9611775 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554752 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554816 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 3523792 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554880 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 554944 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 2050753 d446 d447
private def d441 : MobiusHarmonicTree := .branch 5574545 d442 d445
private def d433 : MobiusHarmonicTree := .branch 15186320 d434 d441
private def d417 : MobiusHarmonicTree := .branch 19004697 d418 d433
private def d385 : MobiusHarmonicTree := .branch 55388517 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555008 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555072 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 1702561 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555136 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555200 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 3775211 d456 d457
private def d451 : MobiusHarmonicTree := .branch 5477772 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555264 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555328 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 4267814 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555392 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555456 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 5159731 d463 d464
private def d458 : MobiusHarmonicTree := .branch 9427545 d459 d462
private def d450 : MobiusHarmonicTree := .branch 14905317 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555520 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555584 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 7703635 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555648 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555712 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 9672387 d471 d472
private def d466 : MobiusHarmonicTree := .branch 17376022 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555776 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555840 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 9259998 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555904 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 555968 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 9157026 d478 d479
private def d473 : MobiusHarmonicTree := .branch 18417024 d474 d477
private def d465 : MobiusHarmonicTree := .branch 35793046 d466 d473
private def d449 : MobiusHarmonicTree := .branch 50698363 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556032 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556096 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 9446226 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556160 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556224 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 10993872 d487 d488
private def d482 : MobiusHarmonicTree := .branch 20440098 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556288 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556352 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 8431805 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556416 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556480 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 9373239 d494 d495
private def d489 : MobiusHarmonicTree := .branch 17805044 d490 d493
private def d481 : MobiusHarmonicTree := .branch 38245142 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556544 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556608 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 8790840 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556672 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556736 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 7438134 d502 d503
private def d497 : MobiusHarmonicTree := .branch 16228974 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556800 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556864 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 2693739 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556928 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock067 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 556992 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 2307150 d509 d510
private def d504 : MobiusHarmonicTree := .branch 5000889 d505 d508
private def d496 : MobiusHarmonicTree := .branch 21229863 d497 d504
private def d480 : MobiusHarmonicTree := .branch 59475005 d481 d496
private def d448 : MobiusHarmonicTree := .branch 110173368 d449 d480
private def d384 : MobiusHarmonicTree := .branch 165561885 d385 d448
private def d256 : MobiusHarmonicTree := .branch 269451822 d257 d384
private def d0 : MobiusHarmonicTree := .branch 711475365 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 540672 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 540672 711475365 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 540672 442023543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 540672 348997646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 540672 164534573 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 540672 80461327 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 540672 45605167 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 540672 26100506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 540672 13296798 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 540800 12803708 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 540928 19504661 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 540928 9979876 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 541056 9524785 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 541184 34856160 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 541184 18976172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 541184 9309973 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 541312 9666199 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 541440 15879988 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 541440 8051745 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 541568 7828243 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 541696 84073246 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 541696 41460442 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 541696 21992635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 541696 11488481 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 541824 10504154 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 541952 19467807 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 541952 9988761 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 542080 9479046 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 542208 42612804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 542208 23625803 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 542208 12112057 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 542336 11513746 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 542464 18987001 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 542464 10161753 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 542592 8825248 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 542720 184463073 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 542720 88169976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 542720 36260808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 542720 17089560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 542720 8399339 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 542848 8690221 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 542976 19171248 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 542976 9047299 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 543104 10123949 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 543232 51909168 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 543232 25581450 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 543232 11678781 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 543360 13902669 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 543488 26327718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 543488 13623492 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 543616 12704226 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 543744 96293097 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 543744 55920763 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 543744 27423799 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 543744 13444108 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 543872 13979691 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 544000 28496964 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 544000 13641872 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 544128 14855092 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 544256 40372334 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 544256 26349762 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 544256 14958266 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 544384 11391496 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 544512 14022572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 544512 8145881 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 544640 5876691 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 544768 93025897 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 544768 45816490 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 544768 30191539 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 544768 19826554 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 544768 9080769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 544768 4438171 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 544896 4642598 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 545024 10745785 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 545024 5368002 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 545152 5377783 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 545280 10364985 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 545280 5863631 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 545280 2919376 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 545408 2944255 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 545536 4501354 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 545536 3313826 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 545664 1187528 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 545792 15624951 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 545792 4662683 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 545792 2027845 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 545792 892229 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 545920 1135616 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 546048 2634838 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 546048 1281844 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 546176 1352994 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 546304 10962268 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 546304 3151274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 546304 728515 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 546432 2422759 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 546560 7810994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 546560 4566269 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 546688 3244725 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 546816 47209407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 546816 15941844 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 546816 9744285 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 546816 3401018 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 546816 2241930 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 546944 1159088 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 547072 6343267 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 547072 2926200 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 547200 3417067 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 547328 6197559 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 547328 4610821 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 547328 3251872 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 547456 1358949 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 547584 1586738 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 547584 818100 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 547712 768638 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 547840 31267563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 547840 20476671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 547840 6859716 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 547840 2529671 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 547968 4330045 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 548096 13616955 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 548096 7247962 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 548224 6368993 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 548352 10790892 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 548352 7824034 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 548352 5373771 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 548480 2450263 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 548608 2966858 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 548608 1314142 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 548736 1652716 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 548864 269451822 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 548864 103889937 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 548864 58031609 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 548864 37857447 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 548864 19025159 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 548864 9728574 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 548864 3816572 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 548992 5912002 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 549120 9296585 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 549120 4870930 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 549248 4425655 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 549376 18832288 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 549376 8214599 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 549376 3327059 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 549504 4887540 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 549632 10617689 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 549632 6027017 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 549760 4590672 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 549888 20174162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 549888 6407375 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 549888 3201750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 549888 1116532 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 550016 2085218 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 550144 3205625 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 550144 1099655 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 550272 2105970 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 550400 13766787 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 550400 9076772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 550400 4171087 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 550528 4905685 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 550656 4690015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 550656 2923518 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 550784 1766497 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 550912 45858328 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 550912 13542964 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 550912 5163860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 550912 2442837 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 550912 1366711 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 551040 1076126 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 551168 2721023 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 551168 1779662 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 551296 941361 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 551424 8379104 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 551424 5492032 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 551424 3457929 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 551552 2034103 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 551680 2887072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 551680 1584137 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 551808 1302935 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 551936 32315364 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 551936 10689002 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 551936 3034063 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 551936 1235517 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 552064 1798546 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 552192 7654939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 552192 3273928 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 552320 4381011 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 552448 21626362 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 552448 10342636 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 552448 5399032 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 552576 4943604 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 552704 11283726 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 552704 5298868 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 552832 5984858 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 552960 165561885 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 552960 55388517 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 552960 36383820 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 552960 26334284 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 552960 17417269 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 552960 10207557 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 553088 7209712 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 553216 8917015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 553216 5149399 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 553344 3767616 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 553472 10049536 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 553472 6631338 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 553472 3752317 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 553600 2879021 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 553728 3418198 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 553728 2425157 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 553856 993041 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 553984 19004697 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 553984 3818377 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 553984 2672824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 553984 1084787 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 554112 1588037 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 554240 1145553 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 554240 611628 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 554368 533925 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 554496 15186320 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 554496 9611775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 554496 3784993 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 554624 5826782 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 554752 5574545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 554752 3523792 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 554880 2050753 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 555008 110173368 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 555008 50698363 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 555008 14905317 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 555008 5477772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 555008 1702561 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 555136 3775211 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 555264 9427545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 555264 4267814 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 555392 5159731 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 555520 35793046 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 555520 17376022 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 555520 7703635 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 555648 9672387 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 555776 18417024 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 555776 9259998 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 555904 9157026 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 556032 59475005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 556032 38245142 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 556032 20440098 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 556032 9446226 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 556160 10993872 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 556288 17805044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 556288 8431805 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 556416 9373239 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 556544 21229863 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 556544 16228974 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 556544 8790840 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 556672 7438134 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 556800 5000889 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 556800 2693739 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 556928 2307150 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 540672 (MobiusHarmonicTree.branch 711475365 mobiusHarmonicBlock066 mobiusHarmonicBlock067) = true := Helfgott.combined

#print axioms solution
