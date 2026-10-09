-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair060_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:35:57.949203+00:00
-- url     : https://prove2.me/submissions/7ba32ba1-4077-4e17-a727-65e25ba71f5b

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983040 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983104 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 19624665 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983168 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983232 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 18294844 d11 d12
private def d6 : MobiusHarmonicTree := .branch 37919509 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983296 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983360 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 18738881 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983424 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983488 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 19287549 d18 d19
private def d13 : MobiusHarmonicTree := .branch 38026430 d14 d17
private def d5 : MobiusHarmonicTree := .branch 75945939 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983552 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983616 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 19877737 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983680 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983744 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 21848222 d26 d27
private def d21 : MobiusHarmonicTree := .branch 41725959 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983808 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983872 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 22445043 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 983936 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984000 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 23228723 d33 d34
private def d28 : MobiusHarmonicTree := .branch 45673766 d29 d32
private def d20 : MobiusHarmonicTree := .branch 87399725 d21 d28
private def d4 : MobiusHarmonicTree := .branch 163345664 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984064 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984128 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 23896345 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984192 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984256 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 24580055 d42 d43
private def d37 : MobiusHarmonicTree := .branch 48476400 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984320 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984384 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 24206096 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984448 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984512 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 23486825 d49 d50
private def d44 : MobiusHarmonicTree := .branch 47692921 d45 d48
private def d36 : MobiusHarmonicTree := .branch 96169321 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984576 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984640 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 23421826 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984704 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984768 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 23126333 d57 d58
private def d52 : MobiusHarmonicTree := .branch 46548159 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984832 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984896 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 23473624 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 984960 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985024 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 23619808 d64 d65
private def d59 : MobiusHarmonicTree := .branch 47093432 d60 d63
private def d51 : MobiusHarmonicTree := .branch 93641591 d52 d59
private def d35 : MobiusHarmonicTree := .branch 189810912 d36 d51
private def d3 : MobiusHarmonicTree := .branch 353156576 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985088 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985152 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 23451273 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985216 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985280 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 23938438 d74 d75
private def d69 : MobiusHarmonicTree := .branch 47389711 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985344 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985408 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 24786749 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985472 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985536 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 24195034 d81 d82
private def d76 : MobiusHarmonicTree := .branch 48981783 d77 d80
private def d68 : MobiusHarmonicTree := .branch 96371494 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985600 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985664 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 23796226 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985728 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985792 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 23537491 d89 d90
private def d84 : MobiusHarmonicTree := .branch 47333717 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985856 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985920 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 24254574 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 985984 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986048 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 23057778 d96 d97
private def d91 : MobiusHarmonicTree := .branch 47312352 d92 d95
private def d83 : MobiusHarmonicTree := .branch 94646069 d84 d91
private def d67 : MobiusHarmonicTree := .branch 191017563 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986112 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986176 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 21351268 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986240 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986304 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 21476181 d105 d106
private def d100 : MobiusHarmonicTree := .branch 42827449 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986368 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986432 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 24339308 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986496 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986560 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 24859180 d112 d113
private def d107 : MobiusHarmonicTree := .branch 49198488 d108 d111
private def d99 : MobiusHarmonicTree := .branch 92025937 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986624 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986688 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 24345166 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986752 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986816 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 23419850 d120 d121
private def d115 : MobiusHarmonicTree := .branch 47765016 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986880 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 986944 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 22674110 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987008 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987072 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 20915509 d127 d128
private def d122 : MobiusHarmonicTree := .branch 43589619 d123 d126
private def d114 : MobiusHarmonicTree := .branch 91354635 d115 d122
private def d98 : MobiusHarmonicTree := .branch 183380572 d99 d114
private def d66 : MobiusHarmonicTree := .branch 374398135 d67 d98
private def d2 : MobiusHarmonicTree := .branch 727554711 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987136 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987200 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 19620190 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987264 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987328 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 21758800 d138 d139
private def d133 : MobiusHarmonicTree := .branch 41378990 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987392 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987456 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 22625877 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987520 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987584 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 22496385 d145 d146
private def d140 : MobiusHarmonicTree := .branch 45122262 d141 d144
private def d132 : MobiusHarmonicTree := .branch 86501252 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987648 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987712 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 22510686 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987776 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987840 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 23367187 d153 d154
private def d148 : MobiusHarmonicTree := .branch 45877873 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987904 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 987968 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 25573778 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988032 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988096 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 25215259 d160 d161
private def d155 : MobiusHarmonicTree := .branch 50789037 d156 d159
private def d147 : MobiusHarmonicTree := .branch 96666910 d148 d155
private def d131 : MobiusHarmonicTree := .branch 183168162 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988160 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988224 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 24490473 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988288 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988352 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 24562193 d169 d170
private def d164 : MobiusHarmonicTree := .branch 49052666 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988416 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988480 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 24605524 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988544 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988608 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 25286154 d176 d177
private def d171 : MobiusHarmonicTree := .branch 49891678 d172 d175
private def d163 : MobiusHarmonicTree := .branch 98944344 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988672 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988736 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 24551624 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988800 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988864 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 25327100 d184 d185
private def d179 : MobiusHarmonicTree := .branch 49878724 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988928 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 988992 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 24999277 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989056 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989120 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 25618804 d191 d192
private def d186 : MobiusHarmonicTree := .branch 50618081 d187 d190
private def d178 : MobiusHarmonicTree := .branch 100496805 d179 d186
private def d162 : MobiusHarmonicTree := .branch 199441149 d163 d178
private def d130 : MobiusHarmonicTree := .branch 382609311 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989184 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989248 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 26517183 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989312 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989376 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 27018105 d201 d202
private def d196 : MobiusHarmonicTree := .branch 53535288 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989440 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989504 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 28331442 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989568 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989632 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 28921944 d208 d209
private def d203 : MobiusHarmonicTree := .branch 57253386 d204 d207
private def d195 : MobiusHarmonicTree := .branch 110788674 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989696 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989760 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 28007882 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989824 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989888 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 28627563 d216 d217
private def d211 : MobiusHarmonicTree := .branch 56635445 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 989952 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990016 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 26935006 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990080 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990144 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 28680732 d223 d224
private def d218 : MobiusHarmonicTree := .branch 55615738 d219 d222
private def d210 : MobiusHarmonicTree := .branch 112251183 d211 d218
private def d194 : MobiusHarmonicTree := .branch 223039857 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990208 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990272 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 30091814 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990336 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990400 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 29651729 d232 d233
private def d227 : MobiusHarmonicTree := .branch 59743543 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990464 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990528 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 29444997 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990592 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990656 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 29691515 d239 d240
private def d234 : MobiusHarmonicTree := .branch 59136512 d235 d238
private def d226 : MobiusHarmonicTree := .branch 118880055 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990720 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990784 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 30137827 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990848 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990912 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 31410505 d247 d248
private def d242 : MobiusHarmonicTree := .branch 61548332 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 990976 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991040 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 32046213 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991104 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock120 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991168 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 32479929 d254 d255
private def d249 : MobiusHarmonicTree := .branch 64526142 d250 d253
private def d241 : MobiusHarmonicTree := .branch 126074474 d242 d249
private def d225 : MobiusHarmonicTree := .branch 244954529 d226 d241
private def d193 : MobiusHarmonicTree := .branch 467994386 d194 d225
private def d129 : MobiusHarmonicTree := .branch 850603697 d130 d193
private def d1 : MobiusHarmonicTree := .branch 1578158408 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991232 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991296 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 33812370 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991360 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991424 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 35374440 d266 d267
private def d261 : MobiusHarmonicTree := .branch 69186810 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991488 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991552 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 34491460 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991616 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991680 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 34825815 d273 d274
private def d268 : MobiusHarmonicTree := .branch 69317275 d269 d272
private def d260 : MobiusHarmonicTree := .branch 138504085 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991744 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991808 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 35623909 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991872 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 991936 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 35850169 d281 d282
private def d276 : MobiusHarmonicTree := .branch 71474078 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992000 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992064 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 36254783 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992128 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992192 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 36706677 d288 d289
private def d283 : MobiusHarmonicTree := .branch 72961460 d284 d287
private def d275 : MobiusHarmonicTree := .branch 144435538 d276 d283
private def d259 : MobiusHarmonicTree := .branch 282939623 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992256 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992320 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 36074141 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992384 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992448 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 36542031 d297 d298
private def d292 : MobiusHarmonicTree := .branch 72616172 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992512 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992576 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 37453139 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992640 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992704 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 38413334 d304 d305
private def d299 : MobiusHarmonicTree := .branch 75866473 d300 d303
private def d291 : MobiusHarmonicTree := .branch 148482645 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992768 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992832 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 38672291 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992896 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 992960 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 38731733 d312 d313
private def d307 : MobiusHarmonicTree := .branch 77404024 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993024 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993088 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 38524367 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993152 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993216 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 37385732 d319 d320
private def d314 : MobiusHarmonicTree := .branch 75910099 d315 d318
private def d306 : MobiusHarmonicTree := .branch 153314123 d307 d314
private def d290 : MobiusHarmonicTree := .branch 301796768 d291 d306
private def d258 : MobiusHarmonicTree := .branch 584736391 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993280 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993344 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 35255758 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993408 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993472 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 34830449 d329 d330
private def d324 : MobiusHarmonicTree := .branch 70086207 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993536 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993600 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 34674993 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993664 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993728 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 35230030 d336 d337
private def d331 : MobiusHarmonicTree := .branch 69905023 d332 d335
private def d323 : MobiusHarmonicTree := .branch 139991230 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993792 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993856 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 35936889 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993920 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 993984 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 33702868 d344 d345
private def d339 : MobiusHarmonicTree := .branch 69639757 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994048 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994112 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 32889714 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994176 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994240 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 34362010 d351 d352
private def d346 : MobiusHarmonicTree := .branch 67251724 d347 d350
private def d338 : MobiusHarmonicTree := .branch 136891481 d339 d346
private def d322 : MobiusHarmonicTree := .branch 276882711 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994304 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994368 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 33268461 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994432 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994496 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 33935839 d360 d361
private def d355 : MobiusHarmonicTree := .branch 67204300 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994560 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994624 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 35380266 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994688 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994752 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 36732830 d367 d368
private def d362 : MobiusHarmonicTree := .branch 72113096 d363 d366
private def d354 : MobiusHarmonicTree := .branch 139317396 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994816 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994880 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 38016750 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 994944 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995008 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 37482190 d375 d376
private def d370 : MobiusHarmonicTree := .branch 75498940 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995072 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995136 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 37968759 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995200 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995264 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 38558699 d382 d383
private def d377 : MobiusHarmonicTree := .branch 76527458 d378 d381
private def d369 : MobiusHarmonicTree := .branch 152026398 d370 d377
private def d353 : MobiusHarmonicTree := .branch 291343794 d354 d369
private def d321 : MobiusHarmonicTree := .branch 568226505 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1152962896 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995328 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995392 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 36882052 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995456 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995520 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 36215322 d393 d394
private def d388 : MobiusHarmonicTree := .branch 73097374 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995584 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995648 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 35037562 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995712 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995776 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 34546020 d400 d401
private def d395 : MobiusHarmonicTree := .branch 69583582 d396 d399
private def d387 : MobiusHarmonicTree := .branch 142680956 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995840 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995904 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 33999346 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 995968 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996032 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 34549160 d408 d409
private def d403 : MobiusHarmonicTree := .branch 68548506 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996096 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996160 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 33384312 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996224 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996288 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 31866383 d415 d416
private def d410 : MobiusHarmonicTree := .branch 65250695 d411 d414
private def d402 : MobiusHarmonicTree := .branch 133799201 d403 d410
private def d386 : MobiusHarmonicTree := .branch 276480157 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996352 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996416 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 31663555 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996480 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996544 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 32368952 d424 d425
private def d419 : MobiusHarmonicTree := .branch 64032507 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996608 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996672 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 31605263 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996736 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996800 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 31894136 d431 d432
private def d426 : MobiusHarmonicTree := .branch 63499399 d427 d430
private def d418 : MobiusHarmonicTree := .branch 127531906 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996864 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996928 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 31721519 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 996992 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997056 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 31156804 d439 d440
private def d434 : MobiusHarmonicTree := .branch 62878323 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997120 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997184 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 30307435 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997248 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997312 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 29317890 d446 d447
private def d441 : MobiusHarmonicTree := .branch 59625325 d442 d445
private def d433 : MobiusHarmonicTree := .branch 122503648 d434 d441
private def d417 : MobiusHarmonicTree := .branch 250035554 d418 d433
private def d385 : MobiusHarmonicTree := .branch 526515711 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997376 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997440 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 28515065 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997504 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997568 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 29900805 d456 d457
private def d451 : MobiusHarmonicTree := .branch 58415870 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997632 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997696 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 28997888 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997760 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997824 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 28626382 d463 d464
private def d458 : MobiusHarmonicTree := .branch 57624270 d459 d462
private def d450 : MobiusHarmonicTree := .branch 116040140 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997888 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 997952 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 27733885 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998016 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998080 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 27310522 d471 d472
private def d466 : MobiusHarmonicTree := .branch 55044407 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998144 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998208 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 25852429 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998272 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998336 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 26444064 d478 d479
private def d473 : MobiusHarmonicTree := .branch 52296493 d474 d477
private def d465 : MobiusHarmonicTree := .branch 107340900 d466 d473
private def d449 : MobiusHarmonicTree := .branch 223381040 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998400 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998464 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 25297955 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998528 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998592 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 25310708 d487 d488
private def d482 : MobiusHarmonicTree := .branch 50608663 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998656 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998720 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 27336050 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998784 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998848 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 27290532 d494 d495
private def d489 : MobiusHarmonicTree := .branch 54626582 d490 d493
private def d481 : MobiusHarmonicTree := .branch 105235245 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998912 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 998976 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 26611328 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999040 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999104 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 27682872 d502 d503
private def d497 : MobiusHarmonicTree := .branch 54294200 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999168 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999232 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 27384120 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999296 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock121 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 999360 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 28986607 d509 d510
private def d504 : MobiusHarmonicTree := .branch 56370727 d505 d508
private def d496 : MobiusHarmonicTree := .branch 110664927 d497 d504
private def d480 : MobiusHarmonicTree := .branch 215900172 d481 d496
private def d448 : MobiusHarmonicTree := .branch 439281212 d449 d480
private def d384 : MobiusHarmonicTree := .branch 965796923 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2118759819 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3696918227 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 983040 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 983040 3696918227 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 983040 1578158408 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 983040 727554711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 983040 353156576 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 983040 163345664 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 983040 75945939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 983040 37919509 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 983040 19624665 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 983168 18294844 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 983296 38026430 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 983296 18738881 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 983424 19287549 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 983552 87399725 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 983552 41725959 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 983552 19877737 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 983680 21848222 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 983808 45673766 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 983808 22445043 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 983936 23228723 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 984064 189810912 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 984064 96169321 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 984064 48476400 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 984064 23896345 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 984192 24580055 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 984320 47692921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 984320 24206096 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 984448 23486825 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 984576 93641591 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 984576 46548159 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 984576 23421826 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 984704 23126333 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 984832 47093432 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 984832 23473624 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 984960 23619808 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 985088 374398135 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 985088 191017563 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 985088 96371494 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 985088 47389711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 985088 23451273 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 985216 23938438 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 985344 48981783 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 985344 24786749 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 985472 24195034 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 985600 94646069 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 985600 47333717 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 985600 23796226 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 985728 23537491 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 985856 47312352 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 985856 24254574 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 985984 23057778 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 986112 183380572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 986112 92025937 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 986112 42827449 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 986112 21351268 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 986240 21476181 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 986368 49198488 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 986368 24339308 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 986496 24859180 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 986624 91354635 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 986624 47765016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 986624 24345166 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 986752 23419850 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 986880 43589619 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 986880 22674110 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 987008 20915509 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 987136 850603697 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 987136 382609311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 987136 183168162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 987136 86501252 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 987136 41378990 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 987136 19620190 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 987264 21758800 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 987392 45122262 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 987392 22625877 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 987520 22496385 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 987648 96666910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 987648 45877873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 987648 22510686 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 987776 23367187 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 987904 50789037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 987904 25573778 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 988032 25215259 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 988160 199441149 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 988160 98944344 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 988160 49052666 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 988160 24490473 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 988288 24562193 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 988416 49891678 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 988416 24605524 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 988544 25286154 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 988672 100496805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 988672 49878724 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 988672 24551624 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 988800 25327100 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 988928 50618081 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 988928 24999277 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 989056 25618804 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 989184 467994386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 989184 223039857 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 989184 110788674 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 989184 53535288 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 989184 26517183 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 989312 27018105 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 989440 57253386 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 989440 28331442 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 989568 28921944 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 989696 112251183 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 989696 56635445 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 989696 28007882 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 989824 28627563 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 989952 55615738 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 989952 26935006 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 990080 28680732 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 990208 244954529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 990208 118880055 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 990208 59743543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 990208 30091814 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 990336 29651729 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 990464 59136512 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 990464 29444997 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 990592 29691515 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 990720 126074474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 990720 61548332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 990720 30137827 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 990848 31410505 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 990976 64526142 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 990976 32046213 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 991104 32479929 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 991232 2118759819 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 991232 1152962896 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 991232 584736391 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 991232 282939623 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 991232 138504085 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 991232 69186810 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 991232 33812370 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 991360 35374440 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 991488 69317275 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 991488 34491460 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 991616 34825815 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 991744 144435538 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 991744 71474078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 991744 35623909 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 991872 35850169 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 992000 72961460 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 992000 36254783 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 992128 36706677 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 992256 301796768 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 992256 148482645 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 992256 72616172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 992256 36074141 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 992384 36542031 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 992512 75866473 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 992512 37453139 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 992640 38413334 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 992768 153314123 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 992768 77404024 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 992768 38672291 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 992896 38731733 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 993024 75910099 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 993024 38524367 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 993152 37385732 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 993280 568226505 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 993280 276882711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 993280 139991230 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 993280 70086207 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 993280 35255758 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 993408 34830449 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 993536 69905023 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 993536 34674993 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 993664 35230030 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 993792 136891481 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 993792 69639757 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 993792 35936889 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 993920 33702868 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 994048 67251724 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 994048 32889714 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 994176 34362010 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 994304 291343794 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 994304 139317396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 994304 67204300 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 994304 33268461 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 994432 33935839 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 994560 72113096 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 994560 35380266 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 994688 36732830 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 994816 152026398 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 994816 75498940 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 994816 38016750 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 994944 37482190 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 995072 76527458 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 995072 37968759 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 995200 38558699 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 995328 965796923 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 995328 526515711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 995328 276480157 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 995328 142680956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 995328 73097374 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 995328 36882052 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 995456 36215322 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 995584 69583582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 995584 35037562 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 995712 34546020 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 995840 133799201 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 995840 68548506 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 995840 33999346 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 995968 34549160 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 996096 65250695 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 996096 33384312 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 996224 31866383 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 996352 250035554 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 996352 127531906 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 996352 64032507 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 996352 31663555 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 996480 32368952 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 996608 63499399 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 996608 31605263 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 996736 31894136 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 996864 122503648 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 996864 62878323 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 996864 31721519 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 996992 31156804 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 997120 59625325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 997120 30307435 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 997248 29317890 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 997376 439281212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 997376 223381040 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 997376 116040140 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 997376 58415870 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 997376 28515065 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 997504 29900805 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 997632 57624270 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 997632 28997888 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 997760 28626382 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 997888 107340900 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 997888 55044407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 997888 27733885 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 998016 27310522 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 998144 52296493 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 998144 25852429 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 998272 26444064 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 998400 215900172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 998400 105235245 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 998400 50608663 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 998400 25297955 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 998528 25310708 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 998656 54626582 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 998656 27336050 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 998784 27290532 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 998912 110664927 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 998912 54294200 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 998912 26611328 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 999040 27682872 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 999168 56370727 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 999168 27384120 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 999296 28986607 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 983040 (MobiusHarmonicTree.branch 3696918227 mobiusHarmonicBlock120 mobiusHarmonicBlock121) = true := Helfgott.combined

#print axioms solution
