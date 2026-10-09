-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair003_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:00:57.545995+00:00
-- url     : https://prove2.me/submissions/0ce90099-a5cb-4f80-9b43-64e21d86835c

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49152 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49216 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 176759522 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49280 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49344 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 168189998 d11 d12
private def d6 : MobiusHarmonicTree := .branch 344949520 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49408 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49472 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 137664020 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49536 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49600 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 123346790 d18 d19
private def d13 : MobiusHarmonicTree := .branch 261010810 d14 d17
private def d5 : MobiusHarmonicTree := .branch 605960330 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49664 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49728 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 113823378 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49792 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49856 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 82240765 d26 d27
private def d21 : MobiusHarmonicTree := .branch 196064143 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49920 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 49984 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 59902841 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50048 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50112 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 51391161 d33 d34
private def d28 : MobiusHarmonicTree := .branch 111294002 d29 d32
private def d20 : MobiusHarmonicTree := .branch 307358145 d21 d28
private def d4 : MobiusHarmonicTree := .branch 913318475 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50176 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50240 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 28502389 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50304 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50368 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 13983454 d42 d43
private def d37 : MobiusHarmonicTree := .branch 42485843 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50432 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50496 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 30330577 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50560 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50624 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 16417460 d49 d50
private def d44 : MobiusHarmonicTree := .branch 46748037 d45 d48
private def d36 : MobiusHarmonicTree := .branch 89233880 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50688 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50752 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 36883662 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50816 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50880 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 44909200 d57 d58
private def d52 : MobiusHarmonicTree := .branch 81792862 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 50944 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51008 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 55148488 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51072 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51136 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 69599211 d64 d65
private def d59 : MobiusHarmonicTree := .branch 124747699 d60 d63
private def d51 : MobiusHarmonicTree := .branch 206540561 d52 d59
private def d35 : MobiusHarmonicTree := .branch 295774441 d36 d51
private def d3 : MobiusHarmonicTree := .branch 1209092916 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51200 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51264 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 64718825 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51328 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51392 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 85228326 d74 d75
private def d69 : MobiusHarmonicTree := .branch 149947151 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51456 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51520 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 63531619 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51584 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51648 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 63548585 d81 d82
private def d76 : MobiusHarmonicTree := .branch 127080204 d77 d80
private def d68 : MobiusHarmonicTree := .branch 277027355 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51712 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51776 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 38172910 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51840 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51904 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 16570378 d89 d90
private def d84 : MobiusHarmonicTree := .branch 54743288 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 51968 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52032 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 21773421 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52096 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52160 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 13653277 d96 d97
private def d91 : MobiusHarmonicTree := .branch 35426698 d92 d95
private def d83 : MobiusHarmonicTree := .branch 90169986 d84 d91
private def d67 : MobiusHarmonicTree := .branch 367197341 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52224 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52288 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 13787221 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52352 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52416 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 20890486 d105 d106
private def d100 : MobiusHarmonicTree := .branch 34677707 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52480 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52544 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 41622350 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52608 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52672 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 45394812 d112 d113
private def d107 : MobiusHarmonicTree := .branch 87017162 d108 d111
private def d99 : MobiusHarmonicTree := .branch 121694869 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52736 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52800 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 40886690 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52864 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52928 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 46029948 d120 d121
private def d115 : MobiusHarmonicTree := .branch 86916638 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 52992 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53056 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 36642199 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53120 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53184 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 34767718 d127 d128
private def d122 : MobiusHarmonicTree := .branch 71409917 d123 d126
private def d114 : MobiusHarmonicTree := .branch 158326555 d115 d122
private def d98 : MobiusHarmonicTree := .branch 280021424 d99 d114
private def d66 : MobiusHarmonicTree := .branch 647218765 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1856311681 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53248 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53312 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 29807741 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53376 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53440 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 25952977 d138 d139
private def d133 : MobiusHarmonicTree := .branch 55760718 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53504 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53568 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 33921704 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53632 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53696 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 22810885 d145 d146
private def d140 : MobiusHarmonicTree := .branch 56732589 d141 d144
private def d132 : MobiusHarmonicTree := .branch 112493307 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53760 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53824 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 46745112 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53888 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 53952 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 51323077 d153 d154
private def d148 : MobiusHarmonicTree := .branch 98068189 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54016 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54080 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 53866445 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54144 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54208 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 79064177 d160 d161
private def d155 : MobiusHarmonicTree := .branch 132930622 d156 d159
private def d147 : MobiusHarmonicTree := .branch 230998811 d148 d155
private def d131 : MobiusHarmonicTree := .branch 343492118 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54272 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54336 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 62489907 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54400 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54464 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 31273679 d169 d170
private def d164 : MobiusHarmonicTree := .branch 93763586 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54528 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54592 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 17715181 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54656 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54720 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 21796684 d176 d177
private def d171 : MobiusHarmonicTree := .branch 39511865 d172 d175
private def d163 : MobiusHarmonicTree := .branch 133275451 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54784 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54848 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 25252950 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54912 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 54976 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 25250434 d184 d185
private def d179 : MobiusHarmonicTree := .branch 50503384 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55040 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55104 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 17622088 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55168 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55232 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 21025932 d191 d192
private def d186 : MobiusHarmonicTree := .branch 38648020 d187 d190
private def d178 : MobiusHarmonicTree := .branch 89151404 d179 d186
private def d162 : MobiusHarmonicTree := .branch 222426855 d163 d178
private def d130 : MobiusHarmonicTree := .branch 565918973 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55296 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55360 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 22251620 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55424 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55488 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 53395410 d201 d202
private def d196 : MobiusHarmonicTree := .branch 75647030 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55552 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55616 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 73846004 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55680 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55744 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 51847990 d208 d209
private def d203 : MobiusHarmonicTree := .branch 125693994 d204 d207
private def d195 : MobiusHarmonicTree := .branch 201341024 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55808 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55872 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 41168395 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 55936 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56000 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 9984131 d216 d217
private def d211 : MobiusHarmonicTree := .branch 51152526 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56064 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56128 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 4453530 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56192 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56256 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 7838869 d223 d224
private def d218 : MobiusHarmonicTree := .branch 12292399 d219 d222
private def d210 : MobiusHarmonicTree := .branch 63444925 d211 d218
private def d194 : MobiusHarmonicTree := .branch 264785949 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56320 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56384 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 7995723 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56448 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56512 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 42934113 d232 d233
private def d227 : MobiusHarmonicTree := .branch 50929836 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56576 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56640 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 70636435 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56704 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56768 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 86700652 d239 d240
private def d234 : MobiusHarmonicTree := .branch 157337087 d235 d238
private def d226 : MobiusHarmonicTree := .branch 208266923 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56832 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56896 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 110616323 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 56960 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57024 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 150110122 d247 d248
private def d242 : MobiusHarmonicTree := .branch 260726445 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57088 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57152 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 156936110 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57216 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock006 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57280 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 137272658 d254 d255
private def d249 : MobiusHarmonicTree := .branch 294208768 d250 d253
private def d241 : MobiusHarmonicTree := .branch 554935213 d242 d249
private def d225 : MobiusHarmonicTree := .branch 763202136 d226 d241
private def d193 : MobiusHarmonicTree := .branch 1027988085 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1593907058 d130 d193
private def d1 : MobiusHarmonicTree := .branch 3450218739 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57344 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57408 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 135699500 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57472 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57536 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 120898618 d266 d267
private def d261 : MobiusHarmonicTree := .branch 256598118 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57600 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57664 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 104559650 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57728 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57792 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 119387019 d273 d274
private def d268 : MobiusHarmonicTree := .branch 223946669 d269 d272
private def d260 : MobiusHarmonicTree := .branch 480544787 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57856 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57920 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 145477514 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 57984 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58048 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 140143702 d281 d282
private def d276 : MobiusHarmonicTree := .branch 285621216 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58112 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58176 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 154046793 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58240 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58304 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 159822334 d288 d289
private def d283 : MobiusHarmonicTree := .branch 313869127 d284 d287
private def d275 : MobiusHarmonicTree := .branch 599490343 d276 d283
private def d259 : MobiusHarmonicTree := .branch 1080035130 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58368 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58432 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 151289143 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58496 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58560 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 137606188 d297 d298
private def d292 : MobiusHarmonicTree := .branch 288895331 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58624 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58688 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 135938876 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58752 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58816 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 135851821 d304 d305
private def d299 : MobiusHarmonicTree := .branch 271790697 d300 d303
private def d291 : MobiusHarmonicTree := .branch 560686028 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58880 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 58944 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 162874712 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59008 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59072 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 195576270 d312 d313
private def d307 : MobiusHarmonicTree := .branch 358450982 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59136 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59200 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 185387917 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59264 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59328 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 189153469 d319 d320
private def d314 : MobiusHarmonicTree := .branch 374541386 d315 d318
private def d306 : MobiusHarmonicTree := .branch 732992368 d307 d314
private def d290 : MobiusHarmonicTree := .branch 1293678396 d291 d306
private def d258 : MobiusHarmonicTree := .branch 2373713526 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59392 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59456 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 215551692 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59520 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59584 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 229275094 d329 d330
private def d324 : MobiusHarmonicTree := .branch 444826786 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59648 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59712 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 227897074 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59776 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59840 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 220005905 d336 d337
private def d331 : MobiusHarmonicTree := .branch 447902979 d332 d335
private def d323 : MobiusHarmonicTree := .branch 892729765 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59904 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 59968 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 187709031 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60032 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60096 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 190458413 d344 d345
private def d339 : MobiusHarmonicTree := .branch 378167444 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60160 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60224 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 180965189 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60288 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60352 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 165320322 d351 d352
private def d346 : MobiusHarmonicTree := .branch 346285511 d347 d350
private def d338 : MobiusHarmonicTree := .branch 724452955 d339 d346
private def d322 : MobiusHarmonicTree := .branch 1617182720 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60416 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60480 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 143907081 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60544 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60608 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 120113572 d360 d361
private def d355 : MobiusHarmonicTree := .branch 264020653 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60672 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60736 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 138584076 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60800 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60864 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 139983293 d367 d368
private def d362 : MobiusHarmonicTree := .branch 278567369 d363 d366
private def d354 : MobiusHarmonicTree := .branch 542588022 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60928 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 60992 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 167925540 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61056 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61120 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 149809446 d375 d376
private def d370 : MobiusHarmonicTree := .branch 317734986 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61184 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61248 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 135614085 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61312 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61376 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 114866285 d382 d383
private def d377 : MobiusHarmonicTree := .branch 250480370 d378 d381
private def d369 : MobiusHarmonicTree := .branch 568215356 d370 d377
private def d353 : MobiusHarmonicTree := .branch 1110803378 d354 d369
private def d321 : MobiusHarmonicTree := .branch 2727986098 d322 d353
private def d257 : MobiusHarmonicTree := .branch 5101699624 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61440 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61504 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 127646629 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61568 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61632 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 141567158 d393 d394
private def d388 : MobiusHarmonicTree := .branch 269213787 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61696 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61760 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 141714669 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61824 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61888 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 128511320 d400 d401
private def d395 : MobiusHarmonicTree := .branch 270225989 d396 d399
private def d387 : MobiusHarmonicTree := .branch 539439776 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 61952 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62016 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 142668366 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62080 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62144 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 146436861 d408 d409
private def d403 : MobiusHarmonicTree := .branch 289105227 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62208 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62272 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 139796207 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62336 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62400 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 124029586 d415 d416
private def d410 : MobiusHarmonicTree := .branch 263825793 d411 d414
private def d402 : MobiusHarmonicTree := .branch 552931020 d403 d410
private def d386 : MobiusHarmonicTree := .branch 1092370796 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62464 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62528 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 97736051 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62592 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62656 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 91582905 d424 d425
private def d419 : MobiusHarmonicTree := .branch 189318956 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62720 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62784 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 69034990 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62848 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62912 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 66710445 d431 d432
private def d426 : MobiusHarmonicTree := .branch 135745435 d427 d430
private def d418 : MobiusHarmonicTree := .branch 325064391 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 62976 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63040 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 79443731 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63104 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63168 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 72569242 d439 d440
private def d434 : MobiusHarmonicTree := .branch 152012973 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63232 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63296 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 67019521 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63360 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63424 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 76233362 d446 d447
private def d441 : MobiusHarmonicTree := .branch 143252883 d442 d445
private def d433 : MobiusHarmonicTree := .branch 295265856 d434 d441
private def d417 : MobiusHarmonicTree := .branch 620330247 d418 d433
private def d385 : MobiusHarmonicTree := .branch 1712701043 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63488 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63552 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 90693813 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63616 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63680 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 119326195 d456 d457
private def d451 : MobiusHarmonicTree := .branch 210020008 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63744 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63808 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 145463948 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63872 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 63936 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 160289837 d463 d464
private def d458 : MobiusHarmonicTree := .branch 305753785 d459 d462
private def d450 : MobiusHarmonicTree := .branch 515773793 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64000 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64064 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 133014125 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64128 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64192 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 104109375 d471 d472
private def d466 : MobiusHarmonicTree := .branch 237123500 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64256 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64320 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 96768790 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64384 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64448 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 86246129 d478 d479
private def d473 : MobiusHarmonicTree := .branch 183014919 d474 d477
private def d465 : MobiusHarmonicTree := .branch 420138419 d466 d473
private def d449 : MobiusHarmonicTree := .branch 935912212 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64512 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64576 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 49944771 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64640 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64704 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 32245695 d487 d488
private def d482 : MobiusHarmonicTree := .branch 82190466 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64768 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64832 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 11845566 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64896 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 64960 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 23441407 d494 d495
private def d489 : MobiusHarmonicTree := .branch 35286973 d490 d493
private def d481 : MobiusHarmonicTree := .branch 117477439 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65024 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65088 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 27705971 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65152 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65216 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 14640041 d502 d503
private def d497 : MobiusHarmonicTree := .branch 42346012 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65280 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65344 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 15046034 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65408 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock007 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65472 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 12508687 d509 d510
private def d504 : MobiusHarmonicTree := .branch 27554721 d505 d508
private def d496 : MobiusHarmonicTree := .branch 69900733 d497 d504
private def d480 : MobiusHarmonicTree := .branch 187378172 d481 d496
private def d448 : MobiusHarmonicTree := .branch 1123290384 d449 d480
private def d384 : MobiusHarmonicTree := .branch 2835991427 d385 d448
private def d256 : MobiusHarmonicTree := .branch 7937691051 d257 d384
private def d0 : MobiusHarmonicTree := .branch 11387909790 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 49152 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 49152 11387909790 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 49152 3450218739 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 49152 1856311681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 49152 1209092916 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 49152 913318475 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 49152 605960330 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 49152 344949520 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 49152 176759522 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 49280 168189998 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 49408 261010810 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 49408 137664020 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 49536 123346790 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 49664 307358145 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 49664 196064143 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 49664 113823378 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 49792 82240765 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 49920 111294002 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 49920 59902841 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 50048 51391161 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 50176 295774441 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 50176 89233880 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 50176 42485843 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 50176 28502389 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 50304 13983454 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 50432 46748037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 50432 30330577 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 50560 16417460 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 50688 206540561 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 50688 81792862 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 50688 36883662 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 50816 44909200 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 50944 124747699 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 50944 55148488 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 51072 69599211 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 51200 647218765 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 51200 367197341 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 51200 277027355 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 51200 149947151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 51200 64718825 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 51328 85228326 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 51456 127080204 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 51456 63531619 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 51584 63548585 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 51712 90169986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 51712 54743288 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 51712 38172910 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 51840 16570378 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 51968 35426698 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 51968 21773421 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 52096 13653277 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 52224 280021424 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 52224 121694869 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 52224 34677707 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 52224 13787221 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 52352 20890486 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 52480 87017162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 52480 41622350 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 52608 45394812 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 52736 158326555 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 52736 86916638 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 52736 40886690 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 52864 46029948 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 52992 71409917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 52992 36642199 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 53120 34767718 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 53248 1593907058 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 53248 565918973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 53248 343492118 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 53248 112493307 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 53248 55760718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 53248 29807741 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 53376 25952977 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 53504 56732589 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 53504 33921704 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 53632 22810885 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 53760 230998811 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 53760 98068189 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 53760 46745112 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 53888 51323077 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 54016 132930622 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 54016 53866445 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 54144 79064177 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 54272 222426855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 54272 133275451 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 54272 93763586 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 54272 62489907 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 54400 31273679 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 54528 39511865 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 54528 17715181 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 54656 21796684 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 54784 89151404 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 54784 50503384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 54784 25252950 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 54912 25250434 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 55040 38648020 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 55040 17622088 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 55168 21025932 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 55296 1027988085 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 55296 264785949 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 55296 201341024 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 55296 75647030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 55296 22251620 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 55424 53395410 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 55552 125693994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 55552 73846004 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 55680 51847990 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 55808 63444925 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 55808 51152526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 55808 41168395 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 55936 9984131 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 56064 12292399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 56064 4453530 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 56192 7838869 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 56320 763202136 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 56320 208266923 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 56320 50929836 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 56320 7995723 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 56448 42934113 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 56576 157337087 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 56576 70636435 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 56704 86700652 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 56832 554935213 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 56832 260726445 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 56832 110616323 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 56960 150110122 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 57088 294208768 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 57088 156936110 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 57216 137272658 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 57344 7937691051 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 57344 5101699624 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 57344 2373713526 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 57344 1080035130 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 57344 480544787 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 57344 256598118 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 57344 135699500 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 57472 120898618 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 57600 223946669 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 57600 104559650 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 57728 119387019 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 57856 599490343 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 57856 285621216 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 57856 145477514 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 57984 140143702 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 58112 313869127 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 58112 154046793 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 58240 159822334 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 58368 1293678396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 58368 560686028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 58368 288895331 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 58368 151289143 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 58496 137606188 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 58624 271790697 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 58624 135938876 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 58752 135851821 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 58880 732992368 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 58880 358450982 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 58880 162874712 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 59008 195576270 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 59136 374541386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 59136 185387917 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 59264 189153469 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 59392 2727986098 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 59392 1617182720 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 59392 892729765 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 59392 444826786 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 59392 215551692 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 59520 229275094 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 59648 447902979 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 59648 227897074 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 59776 220005905 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 59904 724452955 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 59904 378167444 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 59904 187709031 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 60032 190458413 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 60160 346285511 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 60160 180965189 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 60288 165320322 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 60416 1110803378 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 60416 542588022 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 60416 264020653 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 60416 143907081 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 60544 120113572 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 60672 278567369 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 60672 138584076 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 60800 139983293 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 60928 568215356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 60928 317734986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 60928 167925540 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 61056 149809446 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 61184 250480370 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 61184 135614085 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 61312 114866285 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 61440 2835991427 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 61440 1712701043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 61440 1092370796 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 61440 539439776 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 61440 269213787 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 61440 127646629 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 61568 141567158 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 61696 270225989 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 61696 141714669 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 61824 128511320 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 61952 552931020 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 61952 289105227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 61952 142668366 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 62080 146436861 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 62208 263825793 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 62208 139796207 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 62336 124029586 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 62464 620330247 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 62464 325064391 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 62464 189318956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 62464 97736051 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 62592 91582905 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 62720 135745435 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 62720 69034990 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 62848 66710445 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 62976 295265856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 62976 152012973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 62976 79443731 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 63104 72569242 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 63232 143252883 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 63232 67019521 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 63360 76233362 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 63488 1123290384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 63488 935912212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 63488 515773793 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 63488 210020008 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 63488 90693813 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 63616 119326195 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 63744 305753785 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 63744 145463948 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 63872 160289837 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 64000 420138419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 64000 237123500 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 64000 133014125 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 64128 104109375 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 64256 183014919 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 64256 96768790 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 64384 86246129 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 64512 187378172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 64512 117477439 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 64512 82190466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 64512 49944771 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 64640 32245695 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 64768 35286973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 64768 11845566 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 64896 23441407 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 65024 69900733 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 65024 42346012 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 65024 27705971 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 65152 14640041 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 65280 27554721 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 65280 15046034 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 65408 12508687 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 49152 (MobiusHarmonicTree.branch 11387909790 mobiusHarmonicBlock006 mobiusHarmonicBlock007) = true := Helfgott.combined

#print axioms solution
