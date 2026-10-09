-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair015_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:48:23.799586+00:00
-- url     : https://prove2.me/submissions/fe9d71a9-e271-4c94-acdb-239c3a6ff0d6

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245760 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245824 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 9389474 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245888 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 245952 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 2207721 d11 d12
private def d6 : MobiusHarmonicTree := .branch 11597195 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246016 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246080 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 1739321 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246144 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246208 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 1848046 d18 d19
private def d13 : MobiusHarmonicTree := .branch 3587367 d14 d17
private def d5 : MobiusHarmonicTree := .branch 15184562 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246272 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246336 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 4798173 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246400 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246464 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 1891039 d26 d27
private def d21 : MobiusHarmonicTree := .branch 6689212 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246528 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246592 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 1395093 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246656 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246720 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 2950529 d33 d34
private def d28 : MobiusHarmonicTree := .branch 4345622 d29 d32
private def d20 : MobiusHarmonicTree := .branch 11034834 d21 d28
private def d4 : MobiusHarmonicTree := .branch 26219396 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246784 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246848 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 8604784 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246912 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 246976 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 3510808 d42 d43
private def d37 : MobiusHarmonicTree := .branch 12115592 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247040 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247104 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 1679427 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247168 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247232 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 8914593 d49 d50
private def d44 : MobiusHarmonicTree := .branch 10594020 d45 d48
private def d36 : MobiusHarmonicTree := .branch 22709612 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247296 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247360 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 9282534 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247424 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247488 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 7749685 d57 d58
private def d52 : MobiusHarmonicTree := .branch 17032219 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247552 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247616 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 5682229 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247680 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247744 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 5174885 d64 d65
private def d59 : MobiusHarmonicTree := .branch 10857114 d60 d63
private def d51 : MobiusHarmonicTree := .branch 27889333 d52 d59
private def d35 : MobiusHarmonicTree := .branch 50598945 d36 d51
private def d3 : MobiusHarmonicTree := .branch 76818341 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247808 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247872 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 5744968 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 247936 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248000 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 4794562 d74 d75
private def d69 : MobiusHarmonicTree := .branch 10539530 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248064 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248128 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 2595352 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248192 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248256 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 5212319 d81 d82
private def d76 : MobiusHarmonicTree := .branch 7807671 d77 d80
private def d68 : MobiusHarmonicTree := .branch 18347201 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248320 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248384 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 7198633 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248448 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248512 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 9532712 d89 d90
private def d84 : MobiusHarmonicTree := .branch 16731345 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248576 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248640 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 11478597 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248704 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248768 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 7625451 d96 d97
private def d91 : MobiusHarmonicTree := .branch 19104048 d92 d95
private def d83 : MobiusHarmonicTree := .branch 35835393 d84 d91
private def d67 : MobiusHarmonicTree := .branch 54182594 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248832 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248896 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 11518903 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 248960 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249024 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 7389082 d105 d106
private def d100 : MobiusHarmonicTree := .branch 18907985 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249088 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249152 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 7686249 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249216 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249280 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 9210535 d112 d113
private def d107 : MobiusHarmonicTree := .branch 16896784 d108 d111
private def d99 : MobiusHarmonicTree := .branch 35804769 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249344 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249408 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 8011051 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249472 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249536 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 13220383 d120 d121
private def d115 : MobiusHarmonicTree := .branch 21231434 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249600 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249664 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 11880293 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249728 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249792 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 14079577 d127 d128
private def d122 : MobiusHarmonicTree := .branch 25959870 d123 d126
private def d114 : MobiusHarmonicTree := .branch 47191304 d115 d122
private def d98 : MobiusHarmonicTree := .branch 82996073 d99 d114
private def d66 : MobiusHarmonicTree := .branch 137178667 d67 d98
private def d2 : MobiusHarmonicTree := .branch 213997008 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249856 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249920 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 18630042 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 249984 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250048 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 20468005 d138 d139
private def d133 : MobiusHarmonicTree := .branch 39098047 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250112 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250176 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 19035014 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250240 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250304 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 9225116 d145 d146
private def d140 : MobiusHarmonicTree := .branch 28260130 d141 d144
private def d132 : MobiusHarmonicTree := .branch 67358177 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250368 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250432 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 5406879 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250496 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250560 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 1261185 d153 d154
private def d148 : MobiusHarmonicTree := .branch 6668064 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250624 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250688 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 4384178 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250752 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250816 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 940984 d160 d161
private def d155 : MobiusHarmonicTree := .branch 5325162 d156 d159
private def d147 : MobiusHarmonicTree := .branch 11993226 d148 d155
private def d131 : MobiusHarmonicTree := .branch 79351403 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250880 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 250944 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 1665771 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251008 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251072 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 3421284 d169 d170
private def d164 : MobiusHarmonicTree := .branch 5087055 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251136 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251200 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 8232255 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251264 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251328 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 7122605 d176 d177
private def d171 : MobiusHarmonicTree := .branch 15354860 d172 d175
private def d163 : MobiusHarmonicTree := .branch 20441915 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251392 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251456 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 7118512 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251520 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251584 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 11228852 d184 d185
private def d179 : MobiusHarmonicTree := .branch 18347364 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251648 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251712 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 15048875 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251776 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251840 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 12476411 d191 d192
private def d186 : MobiusHarmonicTree := .branch 27525286 d187 d190
private def d178 : MobiusHarmonicTree := .branch 45872650 d179 d186
private def d162 : MobiusHarmonicTree := .branch 66314565 d163 d178
private def d130 : MobiusHarmonicTree := .branch 145665968 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251904 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 251968 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 10624425 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252032 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252096 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 5874961 d201 d202
private def d196 : MobiusHarmonicTree := .branch 16499386 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252160 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252224 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 8655003 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252288 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252352 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 7549072 d208 d209
private def d203 : MobiusHarmonicTree := .branch 16204075 d204 d207
private def d195 : MobiusHarmonicTree := .branch 32703461 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252416 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252480 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 10828676 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252544 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252608 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 12180953 d216 d217
private def d211 : MobiusHarmonicTree := .branch 23009629 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252672 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252736 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 8641350 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252800 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252864 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 14893124 d223 d224
private def d218 : MobiusHarmonicTree := .branch 23534474 d219 d222
private def d210 : MobiusHarmonicTree := .branch 46544103 d211 d218
private def d194 : MobiusHarmonicTree := .branch 79247564 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252928 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 252992 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 10882210 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253056 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253120 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 7044328 d232 d233
private def d227 : MobiusHarmonicTree := .branch 17926538 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253184 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253248 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 2851296 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253312 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253376 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 3323091 d239 d240
private def d234 : MobiusHarmonicTree := .branch 6174387 d235 d238
private def d226 : MobiusHarmonicTree := .branch 24100925 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253440 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253504 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 1412304 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253568 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253632 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 2795233 d247 d248
private def d242 : MobiusHarmonicTree := .branch 4207537 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253696 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253760 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 6821056 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253824 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock030 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253888 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 11083830 d254 d255
private def d249 : MobiusHarmonicTree := .branch 17904886 d250 d253
private def d241 : MobiusHarmonicTree := .branch 22112423 d242 d249
private def d225 : MobiusHarmonicTree := .branch 46213348 d226 d241
private def d193 : MobiusHarmonicTree := .branch 125460912 d194 d225
private def d129 : MobiusHarmonicTree := .branch 271126880 d130 d193
private def d1 : MobiusHarmonicTree := .branch 485123888 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 253952 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254016 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 14042024 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254080 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254144 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 17088835 d266 d267
private def d261 : MobiusHarmonicTree := .branch 31130859 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254208 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254272 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 19490969 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254336 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254400 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 20444123 d273 d274
private def d268 : MobiusHarmonicTree := .branch 39935092 d269 d272
private def d260 : MobiusHarmonicTree := .branch 71065951 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254464 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254528 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 20481330 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254592 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254656 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 18204735 d281 d282
private def d276 : MobiusHarmonicTree := .branch 38686065 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254720 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254784 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 21171044 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254848 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254912 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 21874096 d288 d289
private def d283 : MobiusHarmonicTree := .branch 43045140 d284 d287
private def d275 : MobiusHarmonicTree := .branch 81731205 d276 d283
private def d259 : MobiusHarmonicTree := .branch 152797156 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 254976 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255040 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 28007162 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255104 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255168 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 33197810 d297 d298
private def d292 : MobiusHarmonicTree := .branch 61204972 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255232 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255296 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 33408683 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255360 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255424 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 33599047 d304 d305
private def d299 : MobiusHarmonicTree := .branch 67007730 d300 d303
private def d291 : MobiusHarmonicTree := .branch 128212702 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255488 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255552 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 38039081 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255616 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255680 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 37723303 d312 d313
private def d307 : MobiusHarmonicTree := .branch 75762384 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255744 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255808 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 35401642 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255872 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 255936 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 39338044 d319 d320
private def d314 : MobiusHarmonicTree := .branch 74739686 d315 d318
private def d306 : MobiusHarmonicTree := .branch 150502070 d307 d314
private def d290 : MobiusHarmonicTree := .branch 278714772 d291 d306
private def d258 : MobiusHarmonicTree := .branch 431511928 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256000 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256064 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 38174346 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256128 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256192 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 38908344 d329 d330
private def d324 : MobiusHarmonicTree := .branch 77082690 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256256 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256320 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 38627716 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256384 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256448 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 37231982 d336 d337
private def d331 : MobiusHarmonicTree := .branch 75859698 d332 d335
private def d323 : MobiusHarmonicTree := .branch 152942388 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256512 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256576 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 38803435 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256640 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256704 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 38819396 d344 d345
private def d339 : MobiusHarmonicTree := .branch 77622831 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256768 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256832 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 32792213 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256896 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 256960 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 25782644 d351 d352
private def d346 : MobiusHarmonicTree := .branch 58574857 d347 d350
private def d338 : MobiusHarmonicTree := .branch 136197688 d339 d346
private def d322 : MobiusHarmonicTree := .branch 289140076 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257024 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257088 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 23513616 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257152 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257216 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 23723389 d360 d361
private def d355 : MobiusHarmonicTree := .branch 47237005 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257280 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257344 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 28281291 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257408 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257472 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 27129460 d367 d368
private def d362 : MobiusHarmonicTree := .branch 55410751 d363 d366
private def d354 : MobiusHarmonicTree := .branch 102647756 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257536 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257600 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 27565926 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257664 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257728 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 27509908 d375 d376
private def d370 : MobiusHarmonicTree := .branch 55075834 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257792 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257856 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 29384685 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257920 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 257984 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 28149119 d382 d383
private def d377 : MobiusHarmonicTree := .branch 57533804 d378 d381
private def d369 : MobiusHarmonicTree := .branch 112609638 d370 d377
private def d353 : MobiusHarmonicTree := .branch 215257394 d354 d369
private def d321 : MobiusHarmonicTree := .branch 504397470 d322 d353
private def d257 : MobiusHarmonicTree := .branch 935909398 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258048 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258112 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 27635194 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258176 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258240 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 26936648 d393 d394
private def d388 : MobiusHarmonicTree := .branch 54571842 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258304 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258368 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 23861372 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258432 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258496 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 21056612 d400 d401
private def d395 : MobiusHarmonicTree := .branch 44917984 d396 d399
private def d387 : MobiusHarmonicTree := .branch 99489826 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258560 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258624 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 17508193 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258688 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258752 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 20448059 d408 d409
private def d403 : MobiusHarmonicTree := .branch 37956252 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258816 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258880 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 20913535 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 258944 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259008 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 15030820 d415 d416
private def d410 : MobiusHarmonicTree := .branch 35944355 d411 d414
private def d402 : MobiusHarmonicTree := .branch 73900607 d403 d410
private def d386 : MobiusHarmonicTree := .branch 173390433 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259072 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259136 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 7405492 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259200 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259264 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 8836817 d424 d425
private def d419 : MobiusHarmonicTree := .branch 16242309 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259328 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259392 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 2826036 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259456 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259520 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 1198502 d431 d432
private def d426 : MobiusHarmonicTree := .branch 4024538 d427 d430
private def d418 : MobiusHarmonicTree := .branch 20266847 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259584 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259648 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 1255558 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259712 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259776 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 827709 d439 d440
private def d434 : MobiusHarmonicTree := .branch 2083267 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259840 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259904 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 1289015 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 259968 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260032 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 5460820 d446 d447
private def d441 : MobiusHarmonicTree := .branch 6749835 d442 d445
private def d433 : MobiusHarmonicTree := .branch 8833102 d434 d441
private def d417 : MobiusHarmonicTree := .branch 29099949 d418 d433
private def d385 : MobiusHarmonicTree := .branch 202490382 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260096 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260160 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 2268035 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260224 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260288 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 2551166 d456 d457
private def d451 : MobiusHarmonicTree := .branch 4819201 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260352 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260416 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 2511291 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260480 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260544 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 2448945 d463 d464
private def d458 : MobiusHarmonicTree := .branch 4960236 d459 d462
private def d450 : MobiusHarmonicTree := .branch 9779437 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260608 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260672 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 4058802 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260736 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260800 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 4512977 d471 d472
private def d466 : MobiusHarmonicTree := .branch 8571779 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260864 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260928 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 8094074 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 260992 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261056 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 8239725 d478 d479
private def d473 : MobiusHarmonicTree := .branch 16333799 d474 d477
private def d465 : MobiusHarmonicTree := .branch 24905578 d466 d473
private def d449 : MobiusHarmonicTree := .branch 34685015 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261120 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261184 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 11803838 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261248 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261312 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 14492315 d487 d488
private def d482 : MobiusHarmonicTree := .branch 26296153 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261376 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261440 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 15567758 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261504 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261568 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 13767078 d494 d495
private def d489 : MobiusHarmonicTree := .branch 29334836 d490 d493
private def d481 : MobiusHarmonicTree := .branch 55630989 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261632 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261696 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 13878889 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261760 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261824 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 8333870 d502 d503
private def d497 : MobiusHarmonicTree := .branch 22212759 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261888 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 261952 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 12849532 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262016 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock031 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 262080 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 11908719 d509 d510
private def d504 : MobiusHarmonicTree := .branch 24758251 d505 d508
private def d496 : MobiusHarmonicTree := .branch 46971010 d497 d504
private def d480 : MobiusHarmonicTree := .branch 102601999 d481 d496
private def d448 : MobiusHarmonicTree := .branch 137287014 d449 d480
private def d384 : MobiusHarmonicTree := .branch 339777396 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1275686794 d257 d384
private def d0 : MobiusHarmonicTree := .branch 1760810682 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 245760 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 245760 1760810682 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 245760 485123888 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 245760 213997008 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 245760 76818341 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 245760 26219396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 245760 15184562 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 245760 11597195 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 245760 9389474 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 245888 2207721 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 246016 3587367 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 246016 1739321 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 246144 1848046 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 246272 11034834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 246272 6689212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 246272 4798173 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 246400 1891039 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 246528 4345622 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 246528 1395093 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 246656 2950529 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 246784 50598945 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 246784 22709612 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 246784 12115592 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 246784 8604784 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 246912 3510808 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 247040 10594020 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 247040 1679427 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 247168 8914593 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 247296 27889333 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 247296 17032219 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 247296 9282534 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 247424 7749685 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 247552 10857114 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 247552 5682229 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 247680 5174885 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 247808 137178667 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 247808 54182594 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 247808 18347201 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 247808 10539530 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 247808 5744968 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 247936 4794562 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 248064 7807671 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 248064 2595352 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 248192 5212319 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 248320 35835393 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 248320 16731345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 248320 7198633 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 248448 9532712 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 248576 19104048 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 248576 11478597 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 248704 7625451 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 248832 82996073 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 248832 35804769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 248832 18907985 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 248832 11518903 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 248960 7389082 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 249088 16896784 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 249088 7686249 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 249216 9210535 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 249344 47191304 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 249344 21231434 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 249344 8011051 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 249472 13220383 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 249600 25959870 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 249600 11880293 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 249728 14079577 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 249856 271126880 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 249856 145665968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 249856 79351403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 249856 67358177 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 249856 39098047 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 249856 18630042 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 249984 20468005 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 250112 28260130 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 250112 19035014 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 250240 9225116 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 250368 11993226 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 250368 6668064 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 250368 5406879 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 250496 1261185 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 250624 5325162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 250624 4384178 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 250752 940984 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 250880 66314565 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 250880 20441915 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 250880 5087055 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 250880 1665771 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 251008 3421284 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 251136 15354860 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 251136 8232255 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 251264 7122605 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 251392 45872650 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 251392 18347364 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 251392 7118512 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 251520 11228852 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 251648 27525286 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 251648 15048875 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 251776 12476411 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 251904 125460912 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 251904 79247564 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 251904 32703461 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 251904 16499386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 251904 10624425 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 252032 5874961 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 252160 16204075 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 252160 8655003 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 252288 7549072 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 252416 46544103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 252416 23009629 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 252416 10828676 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 252544 12180953 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 252672 23534474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 252672 8641350 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 252800 14893124 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 252928 46213348 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 252928 24100925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 252928 17926538 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 252928 10882210 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 253056 7044328 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 253184 6174387 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 253184 2851296 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 253312 3323091 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 253440 22112423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 253440 4207537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 253440 1412304 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 253568 2795233 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 253696 17904886 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 253696 6821056 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 253824 11083830 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 253952 1275686794 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 253952 935909398 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 253952 431511928 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 253952 152797156 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 253952 71065951 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 253952 31130859 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 253952 14042024 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 254080 17088835 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 254208 39935092 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 254208 19490969 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 254336 20444123 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 254464 81731205 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 254464 38686065 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 254464 20481330 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 254592 18204735 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 254720 43045140 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 254720 21171044 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 254848 21874096 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 254976 278714772 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 254976 128212702 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 254976 61204972 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 254976 28007162 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 255104 33197810 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 255232 67007730 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 255232 33408683 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 255360 33599047 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 255488 150502070 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 255488 75762384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 255488 38039081 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 255616 37723303 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 255744 74739686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 255744 35401642 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 255872 39338044 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 256000 504397470 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 256000 289140076 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 256000 152942388 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 256000 77082690 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 256000 38174346 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 256128 38908344 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 256256 75859698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 256256 38627716 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 256384 37231982 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 256512 136197688 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 256512 77622831 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 256512 38803435 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 256640 38819396 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 256768 58574857 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 256768 32792213 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 256896 25782644 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 257024 215257394 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 257024 102647756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 257024 47237005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 257024 23513616 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 257152 23723389 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 257280 55410751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 257280 28281291 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 257408 27129460 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 257536 112609638 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 257536 55075834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 257536 27565926 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 257664 27509908 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 257792 57533804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 257792 29384685 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 257920 28149119 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 258048 339777396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 258048 202490382 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 258048 173390433 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 258048 99489826 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 258048 54571842 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 258048 27635194 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 258176 26936648 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 258304 44917984 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 258304 23861372 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 258432 21056612 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 258560 73900607 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 258560 37956252 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 258560 17508193 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 258688 20448059 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 258816 35944355 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 258816 20913535 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 258944 15030820 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 259072 29099949 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 259072 20266847 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 259072 16242309 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 259072 7405492 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 259200 8836817 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 259328 4024538 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 259328 2826036 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 259456 1198502 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 259584 8833102 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 259584 2083267 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 259584 1255558 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 259712 827709 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 259840 6749835 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 259840 1289015 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 259968 5460820 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 260096 137287014 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 260096 34685015 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 260096 9779437 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 260096 4819201 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 260096 2268035 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 260224 2551166 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 260352 4960236 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 260352 2511291 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 260480 2448945 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 260608 24905578 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 260608 8571779 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 260608 4058802 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 260736 4512977 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 260864 16333799 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 260864 8094074 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 260992 8239725 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 261120 102601999 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 261120 55630989 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 261120 26296153 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 261120 11803838 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 261248 14492315 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 261376 29334836 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 261376 15567758 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 261504 13767078 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 261632 46971010 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 261632 22212759 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 261632 13878889 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 261760 8333870 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 261888 24758251 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 261888 12849532 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 262016 11908719 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 245760 (MobiusHarmonicTree.branch 1760810682 mobiusHarmonicBlock030 mobiusHarmonicBlock031) = true := Helfgott.combined

#print axioms solution
