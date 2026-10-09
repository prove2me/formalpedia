-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair057_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:26:11.406587+00:00
-- url     : https://prove2.me/submissions/18458d75-cde2-4372-b68b-65897a0a6803

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933888 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 933952 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 37274980 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934016 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934080 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 38011814 d11 d12
private def d6 : MobiusHarmonicTree := .branch 75286794 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934144 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934208 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 39412073 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934272 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934336 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 39142336 d18 d19
private def d13 : MobiusHarmonicTree := .branch 78554409 d14 d17
private def d5 : MobiusHarmonicTree := .branch 153841203 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934400 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934464 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 38958227 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934528 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934592 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 40596430 d26 d27
private def d21 : MobiusHarmonicTree := .branch 79554657 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934656 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934720 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 39294217 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934784 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934848 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 38948636 d33 d34
private def d28 : MobiusHarmonicTree := .branch 78242853 d29 d32
private def d20 : MobiusHarmonicTree := .branch 157797510 d21 d28
private def d4 : MobiusHarmonicTree := .branch 311638713 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934912 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 934976 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 40164758 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935040 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935104 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 40256567 d42 d43
private def d37 : MobiusHarmonicTree := .branch 80421325 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935168 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935232 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 40843440 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935296 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935360 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 39408447 d49 d50
private def d44 : MobiusHarmonicTree := .branch 80251887 d45 d48
private def d36 : MobiusHarmonicTree := .branch 160673212 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935424 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935488 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 38604544 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935552 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935616 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 39208462 d57 d58
private def d52 : MobiusHarmonicTree := .branch 77813006 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935680 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935744 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 39896679 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935808 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935872 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 39432850 d64 d65
private def d59 : MobiusHarmonicTree := .branch 79329529 d60 d63
private def d51 : MobiusHarmonicTree := .branch 157142535 d52 d59
private def d35 : MobiusHarmonicTree := .branch 317815747 d36 d51
private def d3 : MobiusHarmonicTree := .branch 629454460 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 935936 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936000 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 36755440 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936064 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936128 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 36113740 d74 d75
private def d69 : MobiusHarmonicTree := .branch 72869180 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936192 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936256 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 35961393 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936320 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936384 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 36272602 d81 d82
private def d76 : MobiusHarmonicTree := .branch 72233995 d77 d80
private def d68 : MobiusHarmonicTree := .branch 145103175 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936448 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936512 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 36323139 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936576 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936640 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 36634236 d89 d90
private def d84 : MobiusHarmonicTree := .branch 72957375 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936704 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936768 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 36194744 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936832 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936896 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 34593046 d96 d97
private def d91 : MobiusHarmonicTree := .branch 70787790 d92 d95
private def d83 : MobiusHarmonicTree := .branch 143745165 d84 d91
private def d67 : MobiusHarmonicTree := .branch 288848340 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 936960 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937024 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 33921306 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937088 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937152 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 32725856 d105 d106
private def d100 : MobiusHarmonicTree := .branch 66647162 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937216 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937280 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 32091872 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937344 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937408 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 31628788 d112 d113
private def d107 : MobiusHarmonicTree := .branch 63720660 d108 d111
private def d99 : MobiusHarmonicTree := .branch 130367822 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937472 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937536 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 31619139 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937600 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937664 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 32108583 d120 d121
private def d115 : MobiusHarmonicTree := .branch 63727722 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937728 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937792 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 31658504 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937856 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937920 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 30755382 d127 d128
private def d122 : MobiusHarmonicTree := .branch 62413886 d123 d126
private def d114 : MobiusHarmonicTree := .branch 126141608 d115 d122
private def d98 : MobiusHarmonicTree := .branch 256509430 d99 d114
private def d66 : MobiusHarmonicTree := .branch 545357770 d67 d98
private def d2 : MobiusHarmonicTree := .branch 1174812230 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 937984 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938048 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 32027192 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938112 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938176 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 33741095 d138 d139
private def d133 : MobiusHarmonicTree := .branch 65768287 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938240 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938304 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 32891354 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938368 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938432 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 33203340 d145 d146
private def d140 : MobiusHarmonicTree := .branch 66094694 d141 d144
private def d132 : MobiusHarmonicTree := .branch 131862981 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938496 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938560 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 32376285 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938624 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938688 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 31677279 d153 d154
private def d148 : MobiusHarmonicTree := .branch 64053564 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938752 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938816 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 30339374 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938880 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 938944 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 29309603 d160 d161
private def d155 : MobiusHarmonicTree := .branch 59648977 d156 d159
private def d147 : MobiusHarmonicTree := .branch 123702541 d148 d155
private def d131 : MobiusHarmonicTree := .branch 255565522 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939008 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939072 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 29956258 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939136 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939200 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 29593344 d169 d170
private def d164 : MobiusHarmonicTree := .branch 59549602 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939264 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939328 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 29972578 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939392 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939456 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 29982322 d176 d177
private def d171 : MobiusHarmonicTree := .branch 59954900 d172 d175
private def d163 : MobiusHarmonicTree := .branch 119504502 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939520 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939584 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 28959708 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939648 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939712 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 29095156 d184 d185
private def d179 : MobiusHarmonicTree := .branch 58054864 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939776 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939840 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 29128449 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939904 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 939968 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 28653177 d191 d192
private def d186 : MobiusHarmonicTree := .branch 57781626 d187 d190
private def d178 : MobiusHarmonicTree := .branch 115836490 d179 d186
private def d162 : MobiusHarmonicTree := .branch 235340992 d163 d178
private def d130 : MobiusHarmonicTree := .branch 490906514 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940032 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940096 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 28688663 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940160 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940224 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 28249711 d201 d202
private def d196 : MobiusHarmonicTree := .branch 56938374 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940288 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940352 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 29891001 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940416 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940480 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 29010789 d208 d209
private def d203 : MobiusHarmonicTree := .branch 58901790 d204 d207
private def d195 : MobiusHarmonicTree := .branch 115840164 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940544 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940608 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 29728722 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940672 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940736 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 29030543 d216 d217
private def d211 : MobiusHarmonicTree := .branch 58759265 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940800 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940864 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 28451597 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940928 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 940992 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 29720814 d223 d224
private def d218 : MobiusHarmonicTree := .branch 58172411 d219 d222
private def d210 : MobiusHarmonicTree := .branch 116931676 d211 d218
private def d194 : MobiusHarmonicTree := .branch 232771840 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941056 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941120 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 29772067 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941184 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941248 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 29497085 d232 d233
private def d227 : MobiusHarmonicTree := .branch 59269152 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941312 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941376 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 29632252 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941440 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941504 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 29236285 d239 d240
private def d234 : MobiusHarmonicTree := .branch 58868537 d235 d238
private def d226 : MobiusHarmonicTree := .branch 118137689 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941568 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941632 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 28223411 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941696 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941760 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 29827231 d247 d248
private def d242 : MobiusHarmonicTree := .branch 58050642 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941824 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941888 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 28216829 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 941952 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock114 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942016 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 27355224 d254 d255
private def d249 : MobiusHarmonicTree := .branch 55572053 d250 d253
private def d241 : MobiusHarmonicTree := .branch 113622695 d242 d249
private def d225 : MobiusHarmonicTree := .branch 231760384 d226 d241
private def d193 : MobiusHarmonicTree := .branch 464532224 d194 d225
private def d129 : MobiusHarmonicTree := .branch 955438738 d130 d193
private def d1 : MobiusHarmonicTree := .branch 2130250968 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942080 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942144 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 27699672 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942208 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942272 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 28211660 d266 d267
private def d261 : MobiusHarmonicTree := .branch 55911332 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942336 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942400 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 28772367 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942464 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942528 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 28170076 d273 d274
private def d268 : MobiusHarmonicTree := .branch 56942443 d269 d272
private def d260 : MobiusHarmonicTree := .branch 112853775 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942592 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942656 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 28151369 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942720 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942784 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 28040435 d281 d282
private def d276 : MobiusHarmonicTree := .branch 56191804 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942848 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942912 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 28873416 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 942976 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943040 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 28349887 d288 d289
private def d283 : MobiusHarmonicTree := .branch 57223303 d284 d287
private def d275 : MobiusHarmonicTree := .branch 113415107 d276 d283
private def d259 : MobiusHarmonicTree := .branch 226268882 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943104 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943168 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 29010810 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943232 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943296 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 30221750 d297 d298
private def d292 : MobiusHarmonicTree := .branch 59232560 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943360 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943424 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 29909229 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943488 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943552 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 29758897 d304 d305
private def d299 : MobiusHarmonicTree := .branch 59668126 d300 d303
private def d291 : MobiusHarmonicTree := .branch 118900686 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943616 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943680 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 30622751 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943744 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943808 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 32732335 d312 d313
private def d307 : MobiusHarmonicTree := .branch 63355086 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943872 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 943936 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 32735347 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944000 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944064 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 33257364 d319 d320
private def d314 : MobiusHarmonicTree := .branch 65992711 d315 d318
private def d306 : MobiusHarmonicTree := .branch 129347797 d307 d314
private def d290 : MobiusHarmonicTree := .branch 248248483 d291 d306
private def d258 : MobiusHarmonicTree := .branch 474517365 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944128 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944192 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 31255401 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944256 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944320 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 29876627 d329 d330
private def d324 : MobiusHarmonicTree := .branch 61132028 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944384 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944448 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 30800073 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944512 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944576 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 32214511 d336 d337
private def d331 : MobiusHarmonicTree := .branch 63014584 d332 d335
private def d323 : MobiusHarmonicTree := .branch 124146612 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944640 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944704 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 33483565 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944768 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944832 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 33894994 d344 d345
private def d339 : MobiusHarmonicTree := .branch 67378559 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944896 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 944960 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 35056586 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945024 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945088 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 34613801 d351 d352
private def d346 : MobiusHarmonicTree := .branch 69670387 d347 d350
private def d338 : MobiusHarmonicTree := .branch 137048946 d339 d346
private def d322 : MobiusHarmonicTree := .branch 261195558 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945152 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945216 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 33769104 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945280 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945344 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 33523319 d360 d361
private def d355 : MobiusHarmonicTree := .branch 67292423 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945408 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945472 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 35208918 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945536 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945600 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 34979999 d367 d368
private def d362 : MobiusHarmonicTree := .branch 70188917 d363 d366
private def d354 : MobiusHarmonicTree := .branch 137481340 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945664 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945728 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 34107153 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945792 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945856 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 33141484 d375 d376
private def d370 : MobiusHarmonicTree := .branch 67248637 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945920 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 945984 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 34300851 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946048 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946112 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 34377615 d382 d383
private def d377 : MobiusHarmonicTree := .branch 68678466 d378 d381
private def d369 : MobiusHarmonicTree := .branch 135927103 d370 d377
private def d353 : MobiusHarmonicTree := .branch 273408443 d354 d369
private def d321 : MobiusHarmonicTree := .branch 534604001 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1009121366 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946176 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946240 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 33317235 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946304 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946368 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 31636826 d393 d394
private def d388 : MobiusHarmonicTree := .branch 64954061 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946432 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946496 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 32895066 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946560 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946624 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 32862137 d400 d401
private def d395 : MobiusHarmonicTree := .branch 65757203 d396 d399
private def d387 : MobiusHarmonicTree := .branch 130711264 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946688 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946752 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 31431779 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946816 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946880 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 31277541 d408 d409
private def d403 : MobiusHarmonicTree := .branch 62709320 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 946944 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947008 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 30670376 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947072 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947136 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 28889283 d415 d416
private def d410 : MobiusHarmonicTree := .branch 59559659 d411 d414
private def d402 : MobiusHarmonicTree := .branch 122268979 d403 d410
private def d386 : MobiusHarmonicTree := .branch 252980243 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947200 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947264 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 28051411 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947328 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947392 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 27876584 d424 d425
private def d419 : MobiusHarmonicTree := .branch 55927995 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947456 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947520 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 27636448 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947584 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947648 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 27354112 d431 d432
private def d426 : MobiusHarmonicTree := .branch 54990560 d427 d430
private def d418 : MobiusHarmonicTree := .branch 110918555 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947712 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947776 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 28464610 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947840 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947904 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 28019796 d439 d440
private def d434 : MobiusHarmonicTree := .branch 56484406 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 947968 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948032 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 27096218 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948096 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948160 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 25537989 d446 d447
private def d441 : MobiusHarmonicTree := .branch 52634207 d442 d445
private def d433 : MobiusHarmonicTree := .branch 109118613 d434 d441
private def d417 : MobiusHarmonicTree := .branch 220037168 d418 d433
private def d385 : MobiusHarmonicTree := .branch 473017411 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948224 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948288 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 24328124 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948352 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948416 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 23565689 d456 d457
private def d451 : MobiusHarmonicTree := .branch 47893813 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948480 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948544 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 22254205 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948608 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948672 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 20880871 d463 d464
private def d458 : MobiusHarmonicTree := .branch 43135076 d459 d462
private def d450 : MobiusHarmonicTree := .branch 91028889 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948736 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948800 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 19891526 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948864 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948928 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 19859329 d471 d472
private def d466 : MobiusHarmonicTree := .branch 39750855 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 948992 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949056 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 19349833 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949120 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949184 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 18715104 d478 d479
private def d473 : MobiusHarmonicTree := .branch 38064937 d474 d477
private def d465 : MobiusHarmonicTree := .branch 77815792 d466 d473
private def d449 : MobiusHarmonicTree := .branch 168844681 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949248 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949312 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 17961511 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949376 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949440 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 18074926 d487 d488
private def d482 : MobiusHarmonicTree := .branch 36036437 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949504 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949568 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 17613348 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949632 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949696 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 18224872 d494 d495
private def d489 : MobiusHarmonicTree := .branch 35838220 d490 d493
private def d481 : MobiusHarmonicTree := .branch 71874657 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949760 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949824 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 16421031 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949888 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 949952 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 16145072 d502 d503
private def d497 : MobiusHarmonicTree := .branch 32566103 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950016 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950080 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 16910243 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950144 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock115 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 950208 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 16682707 d509 d510
private def d504 : MobiusHarmonicTree := .branch 33592950 d505 d508
private def d496 : MobiusHarmonicTree := .branch 66159053 d497 d504
private def d480 : MobiusHarmonicTree := .branch 138033710 d481 d496
private def d448 : MobiusHarmonicTree := .branch 306878391 d449 d480
private def d384 : MobiusHarmonicTree := .branch 779895802 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1789017168 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3919268136 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 933888 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 933888 3919268136 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 933888 2130250968 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 933888 1174812230 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 933888 629454460 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 933888 311638713 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 933888 153841203 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 933888 75286794 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 933888 37274980 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 934016 38011814 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 934144 78554409 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 934144 39412073 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 934272 39142336 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 934400 157797510 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 934400 79554657 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 934400 38958227 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 934528 40596430 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 934656 78242853 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 934656 39294217 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 934784 38948636 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 934912 317815747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 934912 160673212 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 934912 80421325 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 934912 40164758 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 935040 40256567 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 935168 80251887 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 935168 40843440 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 935296 39408447 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 935424 157142535 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 935424 77813006 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 935424 38604544 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 935552 39208462 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 935680 79329529 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 935680 39896679 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 935808 39432850 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 935936 545357770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 935936 288848340 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 935936 145103175 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 935936 72869180 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 935936 36755440 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 936064 36113740 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 936192 72233995 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 936192 35961393 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 936320 36272602 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 936448 143745165 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 936448 72957375 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 936448 36323139 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 936576 36634236 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 936704 70787790 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 936704 36194744 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 936832 34593046 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 936960 256509430 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 936960 130367822 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 936960 66647162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 936960 33921306 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 937088 32725856 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 937216 63720660 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 937216 32091872 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 937344 31628788 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 937472 126141608 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 937472 63727722 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 937472 31619139 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 937600 32108583 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 937728 62413886 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 937728 31658504 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 937856 30755382 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 937984 955438738 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 937984 490906514 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 937984 255565522 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 937984 131862981 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 937984 65768287 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 937984 32027192 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 938112 33741095 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 938240 66094694 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 938240 32891354 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 938368 33203340 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 938496 123702541 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 938496 64053564 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 938496 32376285 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 938624 31677279 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 938752 59648977 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 938752 30339374 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 938880 29309603 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 939008 235340992 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 939008 119504502 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 939008 59549602 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 939008 29956258 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 939136 29593344 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 939264 59954900 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 939264 29972578 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 939392 29982322 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 939520 115836490 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 939520 58054864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 939520 28959708 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 939648 29095156 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 939776 57781626 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 939776 29128449 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 939904 28653177 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 940032 464532224 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 940032 232771840 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 940032 115840164 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 940032 56938374 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 940032 28688663 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 940160 28249711 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 940288 58901790 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 940288 29891001 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 940416 29010789 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 940544 116931676 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 940544 58759265 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 940544 29728722 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 940672 29030543 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 940800 58172411 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 940800 28451597 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 940928 29720814 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 941056 231760384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 941056 118137689 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 941056 59269152 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 941056 29772067 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 941184 29497085 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 941312 58868537 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 941312 29632252 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 941440 29236285 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 941568 113622695 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 941568 58050642 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 941568 28223411 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 941696 29827231 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 941824 55572053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 941824 28216829 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 941952 27355224 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 942080 1789017168 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 942080 1009121366 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 942080 474517365 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 942080 226268882 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 942080 112853775 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 942080 55911332 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 942080 27699672 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 942208 28211660 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 942336 56942443 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 942336 28772367 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 942464 28170076 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 942592 113415107 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 942592 56191804 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 942592 28151369 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 942720 28040435 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 942848 57223303 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 942848 28873416 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 942976 28349887 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 943104 248248483 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 943104 118900686 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 943104 59232560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 943104 29010810 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 943232 30221750 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 943360 59668126 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 943360 29909229 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 943488 29758897 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 943616 129347797 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 943616 63355086 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 943616 30622751 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 943744 32732335 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 943872 65992711 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 943872 32735347 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 944000 33257364 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 944128 534604001 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 944128 261195558 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 944128 124146612 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 944128 61132028 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 944128 31255401 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 944256 29876627 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 944384 63014584 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 944384 30800073 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 944512 32214511 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 944640 137048946 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 944640 67378559 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 944640 33483565 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 944768 33894994 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 944896 69670387 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 944896 35056586 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 945024 34613801 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 945152 273408443 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 945152 137481340 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 945152 67292423 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 945152 33769104 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 945280 33523319 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 945408 70188917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 945408 35208918 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 945536 34979999 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 945664 135927103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 945664 67248637 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 945664 34107153 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 945792 33141484 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 945920 68678466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 945920 34300851 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 946048 34377615 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 946176 779895802 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 946176 473017411 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 946176 252980243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 946176 130711264 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 946176 64954061 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 946176 33317235 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 946304 31636826 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 946432 65757203 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 946432 32895066 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 946560 32862137 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 946688 122268979 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 946688 62709320 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 946688 31431779 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 946816 31277541 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 946944 59559659 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 946944 30670376 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 947072 28889283 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 947200 220037168 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 947200 110918555 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 947200 55927995 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 947200 28051411 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 947328 27876584 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 947456 54990560 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 947456 27636448 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 947584 27354112 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 947712 109118613 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 947712 56484406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 947712 28464610 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 947840 28019796 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 947968 52634207 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 947968 27096218 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 948096 25537989 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 948224 306878391 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 948224 168844681 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 948224 91028889 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 948224 47893813 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 948224 24328124 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 948352 23565689 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 948480 43135076 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 948480 22254205 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 948608 20880871 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 948736 77815792 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 948736 39750855 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 948736 19891526 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 948864 19859329 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 948992 38064937 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 948992 19349833 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 949120 18715104 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 949248 138033710 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 949248 71874657 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 949248 36036437 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 949248 17961511 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 949376 18074926 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 949504 35838220 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 949504 17613348 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 949632 18224872 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 949760 66159053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 949760 32566103 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 949760 16421031 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 949888 16145072 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 950016 33592950 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 950016 16910243 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 950144 16682707 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 933888 (MobiusHarmonicTree.branch 3919268136 mobiusHarmonicBlock114 mobiusHarmonicBlock115) = true := Helfgott.combined

#print axioms solution
