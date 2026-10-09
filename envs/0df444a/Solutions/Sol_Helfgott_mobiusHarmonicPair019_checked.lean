-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair019_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T23:04:28.243727+00:00
-- url     : https://prove2.me/submissions/47982d47-ef7a-4d52-8301-b9a5b83614c0

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311296 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311360 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 57567094 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311424 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311488 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 56798357 d11 d12
private def d6 : MobiusHarmonicTree := .branch 114365451 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311552 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311616 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 58376366 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311680 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311744 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 60771096 d18 d19
private def d13 : MobiusHarmonicTree := .branch 119147462 d14 d17
private def d5 : MobiusHarmonicTree := .branch 233512913 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311808 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311872 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 60765423 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 311936 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312000 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 60237287 d26 d27
private def d21 : MobiusHarmonicTree := .branch 121002710 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312064 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312128 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 62461636 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312192 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312256 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 59144094 d33 d34
private def d28 : MobiusHarmonicTree := .branch 121605730 d29 d32
private def d20 : MobiusHarmonicTree := .branch 242608440 d21 d28
private def d4 : MobiusHarmonicTree := .branch 476121353 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312320 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312384 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 53994811 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312448 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312512 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 57757743 d42 d43
private def d37 : MobiusHarmonicTree := .branch 111752554 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312576 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312640 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 55386719 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312704 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312768 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 52857272 d49 d50
private def d44 : MobiusHarmonicTree := .branch 108243991 d45 d48
private def d36 : MobiusHarmonicTree := .branch 219996545 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312832 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312896 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 55117504 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 312960 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313024 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 53200562 d57 d58
private def d52 : MobiusHarmonicTree := .branch 108318066 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313088 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313152 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 53057476 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313216 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313280 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 52687889 d64 d65
private def d59 : MobiusHarmonicTree := .branch 105745365 d60 d63
private def d51 : MobiusHarmonicTree := .branch 214063431 d52 d59
private def d35 : MobiusHarmonicTree := .branch 434059976 d36 d51
private def d3 : MobiusHarmonicTree := .branch 910181329 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313344 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313408 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 50751709 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313472 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313536 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 50418903 d74 d75
private def d69 : MobiusHarmonicTree := .branch 101170612 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313600 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313664 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 46438349 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313728 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313792 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 43420557 d81 d82
private def d76 : MobiusHarmonicTree := .branch 89858906 d77 d80
private def d68 : MobiusHarmonicTree := .branch 191029518 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313856 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313920 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 40389454 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 313984 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314048 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 41054168 d89 d90
private def d84 : MobiusHarmonicTree := .branch 81443622 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314112 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314176 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 44491050 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314240 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314304 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 45347915 d96 d97
private def d91 : MobiusHarmonicTree := .branch 89838965 d92 d95
private def d83 : MobiusHarmonicTree := .branch 171282587 d84 d91
private def d67 : MobiusHarmonicTree := .branch 362312105 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314368 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314432 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 48172699 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314496 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314560 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 50893192 d105 d106
private def d100 : MobiusHarmonicTree := .branch 99065891 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314624 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314688 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 54962573 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314752 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314816 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 53091331 d112 d113
private def d107 : MobiusHarmonicTree := .branch 108053904 d108 d111
private def d99 : MobiusHarmonicTree := .branch 207119795 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314880 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 314944 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 58308781 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315008 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315072 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 59170688 d120 d121
private def d115 : MobiusHarmonicTree := .branch 117479469 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315136 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315200 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 61266129 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315264 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315328 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 57714781 d127 d128
private def d122 : MobiusHarmonicTree := .branch 118980910 d123 d126
private def d114 : MobiusHarmonicTree := .branch 236460379 d115 d122
private def d98 : MobiusHarmonicTree := .branch 443580174 d99 d114
private def d66 : MobiusHarmonicTree := .branch 805892279 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1716073608 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315392 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315456 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 52869764 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315520 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315584 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 50769527 d138 d139
private def d133 : MobiusHarmonicTree := .branch 103639291 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315648 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315712 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 51924028 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315776 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315840 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 53562084 d145 d146
private def d140 : MobiusHarmonicTree := .branch 105486112 d141 d144
private def d132 : MobiusHarmonicTree := .branch 209125403 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315904 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 315968 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 55454959 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316032 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316096 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 56764617 d153 d154
private def d148 : MobiusHarmonicTree := .branch 112219576 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316160 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316224 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 53180869 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316288 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316352 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 48863562 d160 d161
private def d155 : MobiusHarmonicTree := .branch 102044431 d156 d159
private def d147 : MobiusHarmonicTree := .branch 214264007 d148 d155
private def d131 : MobiusHarmonicTree := .branch 423389410 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316416 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316480 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 48094858 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316544 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316608 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 48043814 d169 d170
private def d164 : MobiusHarmonicTree := .branch 96138672 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316672 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316736 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 47519265 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316800 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316864 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 45799028 d176 d177
private def d171 : MobiusHarmonicTree := .branch 93318293 d172 d175
private def d163 : MobiusHarmonicTree := .branch 189456965 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316928 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 316992 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 42635163 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317056 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317120 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 45903882 d184 d185
private def d179 : MobiusHarmonicTree := .branch 88539045 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317184 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317248 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 45630143 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317312 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317376 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 43932397 d191 d192
private def d186 : MobiusHarmonicTree := .branch 89562540 d187 d190
private def d178 : MobiusHarmonicTree := .branch 178101585 d179 d186
private def d162 : MobiusHarmonicTree := .branch 367558550 d163 d178
private def d130 : MobiusHarmonicTree := .branch 790947960 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317440 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317504 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 44030895 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317568 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317632 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 43991473 d201 d202
private def d196 : MobiusHarmonicTree := .branch 88022368 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317696 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317760 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 40137547 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317824 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317888 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 36289603 d208 d209
private def d203 : MobiusHarmonicTree := .branch 76427150 d204 d207
private def d195 : MobiusHarmonicTree := .branch 164449518 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 317952 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318016 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 34746824 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318080 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318144 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 36024558 d216 d217
private def d211 : MobiusHarmonicTree := .branch 70771382 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318208 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318272 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 33057010 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318336 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318400 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 32346099 d223 d224
private def d218 : MobiusHarmonicTree := .branch 65403109 d219 d222
private def d210 : MobiusHarmonicTree := .branch 136174491 d211 d218
private def d194 : MobiusHarmonicTree := .branch 300624009 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318464 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318528 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 34380106 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318592 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318656 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 32662421 d232 d233
private def d227 : MobiusHarmonicTree := .branch 67042527 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318720 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318784 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 31225037 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318848 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318912 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 32874355 d239 d240
private def d234 : MobiusHarmonicTree := .branch 64099392 d235 d238
private def d226 : MobiusHarmonicTree := .branch 131141919 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 318976 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319040 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 32535253 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319104 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319168 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 33590489 d247 d248
private def d242 : MobiusHarmonicTree := .branch 66125742 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319232 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319296 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 37579498 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319360 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock038 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319424 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 39289830 d254 d255
private def d249 : MobiusHarmonicTree := .branch 76869328 d250 d253
private def d241 : MobiusHarmonicTree := .branch 142995070 d242 d249
private def d225 : MobiusHarmonicTree := .branch 274136989 d226 d241
private def d193 : MobiusHarmonicTree := .branch 574760998 d194 d225
private def d129 : MobiusHarmonicTree := .branch 1365708958 d130 d193
private def d1 : MobiusHarmonicTree := .branch 3081782566 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319488 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319552 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 34786398 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319616 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319680 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 34469005 d266 d267
private def d261 : MobiusHarmonicTree := .branch 69255403 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319744 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319808 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 32560325 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319872 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 319936 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 31140998 d273 d274
private def d268 : MobiusHarmonicTree := .branch 63701323 d269 d272
private def d260 : MobiusHarmonicTree := .branch 132956726 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320000 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320064 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 27166731 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320128 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320192 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 24619654 d281 d282
private def d276 : MobiusHarmonicTree := .branch 51786385 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320256 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320320 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 23111405 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320384 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320448 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 21039429 d288 d289
private def d283 : MobiusHarmonicTree := .branch 44150834 d284 d287
private def d275 : MobiusHarmonicTree := .branch 95937219 d276 d283
private def d259 : MobiusHarmonicTree := .branch 228893945 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320512 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320576 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 15201147 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320640 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320704 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 7277942 d297 d298
private def d292 : MobiusHarmonicTree := .branch 22479089 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320768 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320832 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 11678978 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320896 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 320960 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 12627799 d304 d305
private def d299 : MobiusHarmonicTree := .branch 24306777 d300 d303
private def d291 : MobiusHarmonicTree := .branch 46785866 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321024 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321088 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 11999871 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321152 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321216 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 13685598 d312 d313
private def d307 : MobiusHarmonicTree := .branch 25685469 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321280 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321344 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 13782911 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321408 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321472 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 12330887 d319 d320
private def d314 : MobiusHarmonicTree := .branch 26113798 d315 d318
private def d306 : MobiusHarmonicTree := .branch 51799267 d307 d314
private def d290 : MobiusHarmonicTree := .branch 98585133 d291 d306
private def d258 : MobiusHarmonicTree := .branch 327479078 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321536 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321600 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 13358271 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321664 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321728 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 13844137 d329 d330
private def d324 : MobiusHarmonicTree := .branch 27202408 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321792 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321856 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 8805463 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321920 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 321984 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 9286145 d336 d337
private def d331 : MobiusHarmonicTree := .branch 18091608 d332 d335
private def d323 : MobiusHarmonicTree := .branch 45294016 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322048 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322112 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 8155599 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322176 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322240 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 6507888 d344 d345
private def d339 : MobiusHarmonicTree := .branch 14663487 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322304 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322368 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 1898622 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322432 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322496 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 1144181 d351 d352
private def d346 : MobiusHarmonicTree := .branch 3042803 d347 d350
private def d338 : MobiusHarmonicTree := .branch 17706290 d339 d346
private def d322 : MobiusHarmonicTree := .branch 63000306 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322560 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322624 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 6078192 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322688 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322752 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 7894586 d360 d361
private def d355 : MobiusHarmonicTree := .branch 13972778 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322816 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322880 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 8863860 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 322944 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323008 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 11811002 d367 d368
private def d362 : MobiusHarmonicTree := .branch 20674862 d363 d366
private def d354 : MobiusHarmonicTree := .branch 34647640 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323072 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323136 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 9166699 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323200 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323264 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 5008534 d375 d376
private def d370 : MobiusHarmonicTree := .branch 14175233 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323328 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323392 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 4038370 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323456 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323520 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 6617940 d382 d383
private def d377 : MobiusHarmonicTree := .branch 10656310 d378 d381
private def d369 : MobiusHarmonicTree := .branch 24831543 d370 d377
private def d353 : MobiusHarmonicTree := .branch 59479183 d354 d369
private def d321 : MobiusHarmonicTree := .branch 122479489 d322 d353
private def d257 : MobiusHarmonicTree := .branch 449958567 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323584 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323648 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 6145656 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323712 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323776 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 7406387 d393 d394
private def d388 : MobiusHarmonicTree := .branch 13552043 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323840 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323904 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 7530171 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 323968 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324032 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 3765238 d400 d401
private def d395 : MobiusHarmonicTree := .branch 11295409 d396 d399
private def d387 : MobiusHarmonicTree := .branch 24847452 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324096 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324160 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 7557963 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324224 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324288 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 12346899 d408 d409
private def d403 : MobiusHarmonicTree := .branch 19904862 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324352 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324416 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 18790701 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324480 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324544 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 21581009 d415 d416
private def d410 : MobiusHarmonicTree := .branch 40371710 d411 d414
private def d402 : MobiusHarmonicTree := .branch 60276572 d403 d410
private def d386 : MobiusHarmonicTree := .branch 85124024 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324608 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324672 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 26919406 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324736 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324800 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 31228599 d424 d425
private def d419 : MobiusHarmonicTree := .branch 58148005 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324864 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324928 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 31480764 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 324992 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325056 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 36882987 d431 d432
private def d426 : MobiusHarmonicTree := .branch 68363751 d427 d430
private def d418 : MobiusHarmonicTree := .branch 126511756 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325120 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325184 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 33534988 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325248 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325312 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 33795419 d439 d440
private def d434 : MobiusHarmonicTree := .branch 67330407 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325376 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325440 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 27775044 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325504 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325568 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 22063236 d446 d447
private def d441 : MobiusHarmonicTree := .branch 49838280 d442 d445
private def d433 : MobiusHarmonicTree := .branch 117168687 d434 d441
private def d417 : MobiusHarmonicTree := .branch 243680443 d418 d433
private def d385 : MobiusHarmonicTree := .branch 328804467 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325632 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325696 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 18498993 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325760 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325824 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 21106517 d456 d457
private def d451 : MobiusHarmonicTree := .branch 39605510 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325888 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 325952 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 22383879 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326016 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326080 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 23325407 d463 d464
private def d458 : MobiusHarmonicTree := .branch 45709286 d459 d462
private def d450 : MobiusHarmonicTree := .branch 85314796 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326144 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326208 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 30808449 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326272 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326336 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 31434099 d471 d472
private def d466 : MobiusHarmonicTree := .branch 62242548 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326400 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326464 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 26281896 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326528 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326592 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 25695712 d478 d479
private def d473 : MobiusHarmonicTree := .branch 51977608 d474 d477
private def d465 : MobiusHarmonicTree := .branch 114220156 d466 d473
private def d449 : MobiusHarmonicTree := .branch 199534952 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326656 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326720 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 25486795 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326784 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326848 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 23289256 d487 d488
private def d482 : MobiusHarmonicTree := .branch 48776051 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326912 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 326976 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 23689873 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327040 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327104 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 26624732 d494 d495
private def d489 : MobiusHarmonicTree := .branch 50314605 d490 d493
private def d481 : MobiusHarmonicTree := .branch 99090656 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327168 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327232 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 27234656 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327296 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327360 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 24807727 d502 d503
private def d497 : MobiusHarmonicTree := .branch 52042383 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327424 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327488 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 27747422 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327552 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock039 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 327616 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 33380589 d509 d510
private def d504 : MobiusHarmonicTree := .branch 61128011 d505 d508
private def d496 : MobiusHarmonicTree := .branch 113170394 d497 d504
private def d480 : MobiusHarmonicTree := .branch 212261050 d481 d496
private def d448 : MobiusHarmonicTree := .branch 411796002 d449 d480
private def d384 : MobiusHarmonicTree := .branch 740600469 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1190559036 d257 d384
private def d0 : MobiusHarmonicTree := .branch 4272341602 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 311296 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 311296 4272341602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 311296 3081782566 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 311296 1716073608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 311296 910181329 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 311296 476121353 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 311296 233512913 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 311296 114365451 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 311296 57567094 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 311424 56798357 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 311552 119147462 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 311552 58376366 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 311680 60771096 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 311808 242608440 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 311808 121002710 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 311808 60765423 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 311936 60237287 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 312064 121605730 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 312064 62461636 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 312192 59144094 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 312320 434059976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 312320 219996545 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 312320 111752554 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 312320 53994811 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 312448 57757743 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 312576 108243991 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 312576 55386719 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 312704 52857272 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 312832 214063431 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 312832 108318066 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 312832 55117504 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 312960 53200562 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 313088 105745365 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 313088 53057476 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 313216 52687889 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 313344 805892279 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 313344 362312105 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 313344 191029518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 313344 101170612 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 313344 50751709 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 313472 50418903 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 313600 89858906 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 313600 46438349 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 313728 43420557 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 313856 171282587 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 313856 81443622 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 313856 40389454 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 313984 41054168 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 314112 89838965 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 314112 44491050 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 314240 45347915 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 314368 443580174 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 314368 207119795 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 314368 99065891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 314368 48172699 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 314496 50893192 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 314624 108053904 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 314624 54962573 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 314752 53091331 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 314880 236460379 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 314880 117479469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 314880 58308781 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 315008 59170688 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 315136 118980910 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 315136 61266129 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 315264 57714781 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 315392 1365708958 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 315392 790947960 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 315392 423389410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 315392 209125403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 315392 103639291 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 315392 52869764 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 315520 50769527 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 315648 105486112 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 315648 51924028 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 315776 53562084 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 315904 214264007 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 315904 112219576 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 315904 55454959 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 316032 56764617 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 316160 102044431 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 316160 53180869 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 316288 48863562 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 316416 367558550 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 316416 189456965 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 316416 96138672 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 316416 48094858 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 316544 48043814 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 316672 93318293 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 316672 47519265 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 316800 45799028 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 316928 178101585 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 316928 88539045 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 316928 42635163 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 317056 45903882 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 317184 89562540 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 317184 45630143 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 317312 43932397 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 317440 574760998 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 317440 300624009 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 317440 164449518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 317440 88022368 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 317440 44030895 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 317568 43991473 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 317696 76427150 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 317696 40137547 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 317824 36289603 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 317952 136174491 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 317952 70771382 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 317952 34746824 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 318080 36024558 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 318208 65403109 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 318208 33057010 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 318336 32346099 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 318464 274136989 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 318464 131141919 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 318464 67042527 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 318464 34380106 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 318592 32662421 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 318720 64099392 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 318720 31225037 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 318848 32874355 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 318976 142995070 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 318976 66125742 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 318976 32535253 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 319104 33590489 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 319232 76869328 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 319232 37579498 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 319360 39289830 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 319488 1190559036 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 319488 449958567 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 319488 327479078 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 319488 228893945 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 319488 132956726 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 319488 69255403 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 319488 34786398 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 319616 34469005 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 319744 63701323 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 319744 32560325 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 319872 31140998 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 320000 95937219 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 320000 51786385 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 320000 27166731 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 320128 24619654 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 320256 44150834 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 320256 23111405 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 320384 21039429 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 320512 98585133 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 320512 46785866 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 320512 22479089 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 320512 15201147 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 320640 7277942 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 320768 24306777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 320768 11678978 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 320896 12627799 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 321024 51799267 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 321024 25685469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 321024 11999871 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 321152 13685598 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 321280 26113798 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 321280 13782911 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 321408 12330887 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 321536 122479489 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 321536 63000306 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 321536 45294016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 321536 27202408 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 321536 13358271 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 321664 13844137 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 321792 18091608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 321792 8805463 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 321920 9286145 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 322048 17706290 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 322048 14663487 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 322048 8155599 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 322176 6507888 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 322304 3042803 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 322304 1898622 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 322432 1144181 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 322560 59479183 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 322560 34647640 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 322560 13972778 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 322560 6078192 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 322688 7894586 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 322816 20674862 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 322816 8863860 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 322944 11811002 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 323072 24831543 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 323072 14175233 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 323072 9166699 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 323200 5008534 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 323328 10656310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 323328 4038370 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 323456 6617940 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 323584 740600469 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 323584 328804467 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 323584 85124024 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 323584 24847452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 323584 13552043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 323584 6145656 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 323712 7406387 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 323840 11295409 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 323840 7530171 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 323968 3765238 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 324096 60276572 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 324096 19904862 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 324096 7557963 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 324224 12346899 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 324352 40371710 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 324352 18790701 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 324480 21581009 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 324608 243680443 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 324608 126511756 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 324608 58148005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 324608 26919406 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 324736 31228599 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 324864 68363751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 324864 31480764 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 324992 36882987 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 325120 117168687 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 325120 67330407 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 325120 33534988 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 325248 33795419 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 325376 49838280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 325376 27775044 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 325504 22063236 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 325632 411796002 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 325632 199534952 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 325632 85314796 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 325632 39605510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 325632 18498993 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 325760 21106517 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 325888 45709286 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 325888 22383879 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 326016 23325407 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 326144 114220156 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 326144 62242548 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 326144 30808449 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 326272 31434099 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 326400 51977608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 326400 26281896 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 326528 25695712 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 326656 212261050 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 326656 99090656 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 326656 48776051 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 326656 25486795 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 326784 23289256 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 326912 50314605 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 326912 23689873 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 327040 26624732 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 327168 113170394 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 327168 52042383 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 327168 27234656 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 327296 24807727 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 327424 61128011 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 327424 27747422 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 327552 33380589 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 311296 (MobiusHarmonicTree.branch 4272341602 mobiusHarmonicBlock038 mobiusHarmonicBlock039) = true := Helfgott.combined

#print axioms solution
