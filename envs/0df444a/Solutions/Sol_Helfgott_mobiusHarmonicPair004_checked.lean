-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair004_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:03:33.067285+00:00
-- url     : https://prove2.me/submissions/b4cb456e-c023-469d-85c5-2cf23686bdc2

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65536 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65600 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 21403534 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65664 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65728 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 9645745 d11 d12
private def d6 : MobiusHarmonicTree := .branch 31049279 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65792 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65856 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 4403562 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65920 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 65984 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 10713565 d18 d19
private def d13 : MobiusHarmonicTree := .branch 15117127 d14 d17
private def d5 : MobiusHarmonicTree := .branch 46166406 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66048 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66112 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 21761288 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66176 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66240 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 49936266 d26 d27
private def d21 : MobiusHarmonicTree := .branch 71697554 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66304 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66368 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 66267186 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66432 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66496 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 63540755 d33 d34
private def d28 : MobiusHarmonicTree := .branch 129807941 d29 d32
private def d20 : MobiusHarmonicTree := .branch 201505495 d21 d28
private def d4 : MobiusHarmonicTree := .branch 247671901 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66560 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66624 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 53071581 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66688 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66752 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 68882336 d42 d43
private def d37 : MobiusHarmonicTree := .branch 121953917 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66816 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66880 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 73014840 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 66944 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67008 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 53186676 d49 d50
private def d44 : MobiusHarmonicTree := .branch 126201516 d45 d48
private def d36 : MobiusHarmonicTree := .branch 248155433 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67072 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67136 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 68501911 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67200 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67264 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 65710645 d57 d58
private def d52 : MobiusHarmonicTree := .branch 134212556 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67328 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67392 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 64697846 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67456 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67520 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 52608045 d64 d65
private def d59 : MobiusHarmonicTree := .branch 117305891 d60 d63
private def d51 : MobiusHarmonicTree := .branch 251518447 d52 d59
private def d35 : MobiusHarmonicTree := .branch 499673880 d36 d51
private def d3 : MobiusHarmonicTree := .branch 747345781 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67584 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67648 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 51634373 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67712 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67776 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 44342454 d74 d75
private def d69 : MobiusHarmonicTree := .branch 95976827 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67840 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67904 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 36301706 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 67968 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68032 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 37140531 d81 d82
private def d76 : MobiusHarmonicTree := .branch 73442237 d77 d80
private def d68 : MobiusHarmonicTree := .branch 169419064 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68096 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68160 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 49749780 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68224 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68288 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 58469349 d89 d90
private def d84 : MobiusHarmonicTree := .branch 108219129 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68352 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68416 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 82129376 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68480 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68544 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 77876698 d96 d97
private def d91 : MobiusHarmonicTree := .branch 160006074 d92 d95
private def d83 : MobiusHarmonicTree := .branch 268225203 d84 d91
private def d67 : MobiusHarmonicTree := .branch 437644267 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68608 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68672 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 93008256 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68736 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68800 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 92164797 d105 d106
private def d100 : MobiusHarmonicTree := .branch 185173053 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68864 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68928 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 97768947 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 68992 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69056 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 115455158 d112 d113
private def d107 : MobiusHarmonicTree := .branch 213224105 d108 d111
private def d99 : MobiusHarmonicTree := .branch 398397158 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69120 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69184 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 123712704 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69248 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69312 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 125806107 d120 d121
private def d115 : MobiusHarmonicTree := .branch 249518811 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69376 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69440 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 143103824 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69504 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69568 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 159884710 d127 d128
private def d122 : MobiusHarmonicTree := .branch 302988534 d123 d126
private def d114 : MobiusHarmonicTree := .branch 552507345 d115 d122
private def d98 : MobiusHarmonicTree := .branch 950904503 d99 d114
private def d66 : MobiusHarmonicTree := .branch 1388548770 d67 d98
private def d2 : MobiusHarmonicTree := .branch 2135894551 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69632 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69696 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 158965468 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69760 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69824 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 142677013 d138 d139
private def d133 : MobiusHarmonicTree := .branch 301642481 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69888 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 69952 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 140312849 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70016 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70080 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 133435586 d145 d146
private def d140 : MobiusHarmonicTree := .branch 273748435 d141 d144
private def d132 : MobiusHarmonicTree := .branch 575390916 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70144 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70208 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 108125766 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70272 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70336 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 111152107 d153 d154
private def d148 : MobiusHarmonicTree := .branch 219277873 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70400 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70464 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 101389855 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70528 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70592 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 84898807 d160 d161
private def d155 : MobiusHarmonicTree := .branch 186288662 d156 d159
private def d147 : MobiusHarmonicTree := .branch 405566535 d148 d155
private def d131 : MobiusHarmonicTree := .branch 980957451 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70656 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70720 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 94906272 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70784 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70848 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 105326180 d169 d170
private def d164 : MobiusHarmonicTree := .branch 200232452 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70912 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 70976 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 93741763 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71040 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71104 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 88518593 d176 d177
private def d171 : MobiusHarmonicTree := .branch 182260356 d172 d175
private def d163 : MobiusHarmonicTree := .branch 382492808 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71168 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71232 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 82785561 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71296 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71360 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 58906244 d184 d185
private def d179 : MobiusHarmonicTree := .branch 141691805 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71424 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71488 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 37447117 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71552 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71616 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 38718326 d191 d192
private def d186 : MobiusHarmonicTree := .branch 76165443 d187 d190
private def d178 : MobiusHarmonicTree := .branch 217857248 d179 d186
private def d162 : MobiusHarmonicTree := .branch 600350056 d163 d178
private def d130 : MobiusHarmonicTree := .branch 1581307507 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71680 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71744 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 58832145 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71808 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71872 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 50108607 d201 d202
private def d196 : MobiusHarmonicTree := .branch 108940752 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 71936 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72000 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 45149395 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72064 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72128 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 57009792 d208 d209
private def d203 : MobiusHarmonicTree := .branch 102159187 d204 d207
private def d195 : MobiusHarmonicTree := .branch 211099939 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72192 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72256 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 58958030 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72320 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72384 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 72614456 d216 d217
private def d211 : MobiusHarmonicTree := .branch 131572486 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72448 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72512 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 71520200 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72576 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72640 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 69481328 d223 d224
private def d218 : MobiusHarmonicTree := .branch 141001528 d219 d222
private def d210 : MobiusHarmonicTree := .branch 272574014 d211 d218
private def d194 : MobiusHarmonicTree := .branch 483673953 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72704 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72768 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 63942800 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72832 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72896 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 48732804 d232 d233
private def d227 : MobiusHarmonicTree := .branch 112675604 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 72960 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73024 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 29170411 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73088 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73152 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 45120453 d239 d240
private def d234 : MobiusHarmonicTree := .branch 74290864 d235 d238
private def d226 : MobiusHarmonicTree := .branch 186966468 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73216 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73280 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 68695419 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73344 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73408 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 66599974 d247 d248
private def d242 : MobiusHarmonicTree := .branch 135295393 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73472 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73536 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 63125722 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73600 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock008 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73664 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 63912403 d254 d255
private def d249 : MobiusHarmonicTree := .branch 127038125 d250 d253
private def d241 : MobiusHarmonicTree := .branch 262333518 d242 d249
private def d225 : MobiusHarmonicTree := .branch 449299986 d226 d241
private def d193 : MobiusHarmonicTree := .branch 932973939 d194 d225
private def d129 : MobiusHarmonicTree := .branch 2514281446 d130 d193
private def d1 : MobiusHarmonicTree := .branch 4650175997 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73728 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73792 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 75318864 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73856 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73920 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 88866883 d266 d267
private def d261 : MobiusHarmonicTree := .branch 164185747 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 73984 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74048 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 89793504 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74112 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74176 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 85610373 d273 d274
private def d268 : MobiusHarmonicTree := .branch 175403877 d269 d272
private def d260 : MobiusHarmonicTree := .branch 339589624 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74240 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74304 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 73444003 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74368 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74432 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 73502357 d281 d282
private def d276 : MobiusHarmonicTree := .branch 146946360 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74496 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74560 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 64620730 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74624 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74688 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 71309660 d288 d289
private def d283 : MobiusHarmonicTree := .branch 135930390 d284 d287
private def d275 : MobiusHarmonicTree := .branch 282876750 d276 d283
private def d259 : MobiusHarmonicTree := .branch 622466374 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74752 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74816 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 63786332 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74880 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 74944 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 46887094 d297 d298
private def d292 : MobiusHarmonicTree := .branch 110673426 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75008 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75072 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 43318709 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75136 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75200 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 56479086 d304 d305
private def d299 : MobiusHarmonicTree := .branch 99797795 d300 d303
private def d291 : MobiusHarmonicTree := .branch 210471221 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75264 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75328 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 40384378 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75392 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75456 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 40421149 d312 d313
private def d307 : MobiusHarmonicTree := .branch 80805527 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75520 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75584 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 23683759 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75648 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75712 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 10502871 d319 d320
private def d314 : MobiusHarmonicTree := .branch 34186630 d315 d318
private def d306 : MobiusHarmonicTree := .branch 114992157 d307 d314
private def d290 : MobiusHarmonicTree := .branch 325463378 d291 d306
private def d258 : MobiusHarmonicTree := .branch 947929752 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75776 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75840 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 7276958 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75904 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 75968 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 5780377 d329 d330
private def d324 : MobiusHarmonicTree := .branch 13057335 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76032 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76096 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 4534339 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76160 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76224 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 5194080 d336 d337
private def d331 : MobiusHarmonicTree := .branch 9728419 d332 d335
private def d323 : MobiusHarmonicTree := .branch 22785754 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76288 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76352 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 8096038 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76416 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76480 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 15194971 d344 d345
private def d339 : MobiusHarmonicTree := .branch 23291009 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76544 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76608 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 17905815 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76672 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76736 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 26807416 d351 d352
private def d346 : MobiusHarmonicTree := .branch 44713231 d347 d350
private def d338 : MobiusHarmonicTree := .branch 68004240 d339 d346
private def d322 : MobiusHarmonicTree := .branch 90789994 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76800 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76864 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 21909758 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76928 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 76992 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 25823366 d360 d361
private def d355 : MobiusHarmonicTree := .branch 47733124 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77056 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77120 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 13758591 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77184 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77248 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 10575736 d367 d368
private def d362 : MobiusHarmonicTree := .branch 24334327 d363 d366
private def d354 : MobiusHarmonicTree := .branch 72067451 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77312 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77376 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 16104209 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77440 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77504 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 12930523 d375 d376
private def d370 : MobiusHarmonicTree := .branch 29034732 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77568 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77632 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 2486284 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77696 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77760 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 13050702 d382 d383
private def d377 : MobiusHarmonicTree := .branch 15536986 d378 d381
private def d369 : MobiusHarmonicTree := .branch 44571718 d370 d377
private def d353 : MobiusHarmonicTree := .branch 116639169 d354 d369
private def d321 : MobiusHarmonicTree := .branch 207429163 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1155358915 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77824 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77888 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 8756763 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 77952 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78016 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 7944958 d393 d394
private def d388 : MobiusHarmonicTree := .branch 16701721 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78080 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78144 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 6002999 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78208 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78272 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 6271317 d400 d401
private def d395 : MobiusHarmonicTree := .branch 12274316 d396 d399
private def d387 : MobiusHarmonicTree := .branch 28976037 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78336 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78400 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 8876095 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78464 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78528 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 13679938 d408 d409
private def d403 : MobiusHarmonicTree := .branch 22556033 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78592 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78656 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 2720470 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78720 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78784 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 19443489 d415 d416
private def d410 : MobiusHarmonicTree := .branch 22163959 d411 d414
private def d402 : MobiusHarmonicTree := .branch 44719992 d403 d410
private def d386 : MobiusHarmonicTree := .branch 73696029 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78848 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78912 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 17551247 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 78976 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79040 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 30754029 d424 d425
private def d419 : MobiusHarmonicTree := .branch 48305276 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79104 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79168 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 32955928 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79232 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79296 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 31264236 d431 d432
private def d426 : MobiusHarmonicTree := .branch 64220164 d427 d430
private def d418 : MobiusHarmonicTree := .branch 112525440 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79360 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79424 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 21379065 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79488 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79552 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 15264110 d439 d440
private def d434 : MobiusHarmonicTree := .branch 36643175 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79616 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79680 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 3526760 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79744 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79808 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 10035581 d446 d447
private def d441 : MobiusHarmonicTree := .branch 13562341 d442 d445
private def d433 : MobiusHarmonicTree := .branch 50205516 d434 d441
private def d417 : MobiusHarmonicTree := .branch 162730956 d418 d433
private def d385 : MobiusHarmonicTree := .branch 236426985 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79872 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 79936 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 2839819 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80000 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80064 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 5171037 d456 d457
private def d451 : MobiusHarmonicTree := .branch 8010856 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80128 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80192 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 8282143 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80256 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80320 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 9260337 d463 d464
private def d458 : MobiusHarmonicTree := .branch 17542480 d459 d462
private def d450 : MobiusHarmonicTree := .branch 25553336 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80384 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80448 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 17688284 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80512 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80576 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 20986652 d471 d472
private def d466 : MobiusHarmonicTree := .branch 38674936 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80640 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80704 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 18328427 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80768 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80832 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 6073337 d478 d479
private def d473 : MobiusHarmonicTree := .branch 24401764 d474 d477
private def d465 : MobiusHarmonicTree := .branch 63076700 d466 d473
private def d449 : MobiusHarmonicTree := .branch 88630036 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80896 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 80960 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 4483911 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81024 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81088 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 19804161 d487 d488
private def d482 : MobiusHarmonicTree := .branch 24288072 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81152 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81216 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 20255996 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81280 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81344 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 19151858 d494 d495
private def d489 : MobiusHarmonicTree := .branch 39407854 d490 d493
private def d481 : MobiusHarmonicTree := .branch 63695926 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81408 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81472 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 25173557 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81536 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81600 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 35133713 d502 d503
private def d497 : MobiusHarmonicTree := .branch 60307270 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81664 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81728 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 47645942 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81792 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock009 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 81856 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 39034879 d509 d510
private def d504 : MobiusHarmonicTree := .branch 86680821 d505 d508
private def d496 : MobiusHarmonicTree := .branch 146988091 d497 d504
private def d480 : MobiusHarmonicTree := .branch 210684017 d481 d496
private def d448 : MobiusHarmonicTree := .branch 299314053 d449 d480
private def d384 : MobiusHarmonicTree := .branch 535741038 d385 d448
private def d256 : MobiusHarmonicTree := .branch 1691099953 d257 d384
private def d0 : MobiusHarmonicTree := .branch 6341275950 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 65536 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 65536 6341275950 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 65536 4650175997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 65536 2135894551 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 65536 747345781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 65536 247671901 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 65536 46166406 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 65536 31049279 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 65536 21403534 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 65664 9645745 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 65792 15117127 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 65792 4403562 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 65920 10713565 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 66048 201505495 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 66048 71697554 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 66048 21761288 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 66176 49936266 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 66304 129807941 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 66304 66267186 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 66432 63540755 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 66560 499673880 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 66560 248155433 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 66560 121953917 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 66560 53071581 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 66688 68882336 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 66816 126201516 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 66816 73014840 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 66944 53186676 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 67072 251518447 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 67072 134212556 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 67072 68501911 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 67200 65710645 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 67328 117305891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 67328 64697846 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 67456 52608045 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 67584 1388548770 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 67584 437644267 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 67584 169419064 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 67584 95976827 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 67584 51634373 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 67712 44342454 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 67840 73442237 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 67840 36301706 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 67968 37140531 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 68096 268225203 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 68096 108219129 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 68096 49749780 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 68224 58469349 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 68352 160006074 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 68352 82129376 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 68480 77876698 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 68608 950904503 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 68608 398397158 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 68608 185173053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 68608 93008256 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 68736 92164797 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 68864 213224105 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 68864 97768947 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 68992 115455158 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 69120 552507345 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 69120 249518811 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 69120 123712704 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 69248 125806107 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 69376 302988534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 69376 143103824 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 69504 159884710 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 69632 2514281446 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 69632 1581307507 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 69632 980957451 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 69632 575390916 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 69632 301642481 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 69632 158965468 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 69760 142677013 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 69888 273748435 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 69888 140312849 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 70016 133435586 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 70144 405566535 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 70144 219277873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 70144 108125766 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 70272 111152107 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 70400 186288662 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 70400 101389855 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 70528 84898807 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 70656 600350056 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 70656 382492808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 70656 200232452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 70656 94906272 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 70784 105326180 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 70912 182260356 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 70912 93741763 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 71040 88518593 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 71168 217857248 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 71168 141691805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 71168 82785561 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 71296 58906244 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 71424 76165443 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 71424 37447117 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 71552 38718326 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 71680 932973939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 71680 483673953 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 71680 211099939 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 71680 108940752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 71680 58832145 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 71808 50108607 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 71936 102159187 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 71936 45149395 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 72064 57009792 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 72192 272574014 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 72192 131572486 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 72192 58958030 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 72320 72614456 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 72448 141001528 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 72448 71520200 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 72576 69481328 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 72704 449299986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 72704 186966468 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 72704 112675604 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 72704 63942800 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 72832 48732804 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 72960 74290864 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 72960 29170411 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 73088 45120453 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 73216 262333518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 73216 135295393 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 73216 68695419 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 73344 66599974 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 73472 127038125 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 73472 63125722 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 73600 63912403 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 73728 1691099953 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 73728 1155358915 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 73728 947929752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 73728 622466374 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 73728 339589624 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 73728 164185747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 73728 75318864 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 73856 88866883 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 73984 175403877 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 73984 89793504 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 74112 85610373 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 74240 282876750 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 74240 146946360 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 74240 73444003 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 74368 73502357 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 74496 135930390 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 74496 64620730 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 74624 71309660 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 74752 325463378 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 74752 210471221 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 74752 110673426 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 74752 63786332 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 74880 46887094 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 75008 99797795 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 75008 43318709 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 75136 56479086 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 75264 114992157 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 75264 80805527 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 75264 40384378 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 75392 40421149 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 75520 34186630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 75520 23683759 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 75648 10502871 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 75776 207429163 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 75776 90789994 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 75776 22785754 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 75776 13057335 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 75776 7276958 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 75904 5780377 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 76032 9728419 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 76032 4534339 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 76160 5194080 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 76288 68004240 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 76288 23291009 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 76288 8096038 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 76416 15194971 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 76544 44713231 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 76544 17905815 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 76672 26807416 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 76800 116639169 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 76800 72067451 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 76800 47733124 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 76800 21909758 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 76928 25823366 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 77056 24334327 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 77056 13758591 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 77184 10575736 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 77312 44571718 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 77312 29034732 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 77312 16104209 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 77440 12930523 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 77568 15536986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 77568 2486284 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 77696 13050702 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 77824 535741038 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 77824 236426985 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 77824 73696029 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 77824 28976037 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 77824 16701721 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 77824 8756763 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 77952 7944958 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 78080 12274316 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 78080 6002999 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 78208 6271317 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 78336 44719992 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 78336 22556033 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 78336 8876095 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 78464 13679938 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 78592 22163959 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 78592 2720470 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 78720 19443489 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 78848 162730956 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 78848 112525440 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 78848 48305276 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 78848 17551247 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 78976 30754029 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 79104 64220164 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 79104 32955928 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 79232 31264236 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 79360 50205516 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 79360 36643175 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 79360 21379065 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 79488 15264110 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 79616 13562341 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 79616 3526760 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 79744 10035581 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 79872 299314053 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 79872 88630036 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 79872 25553336 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 79872 8010856 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 79872 2839819 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 80000 5171037 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 80128 17542480 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 80128 8282143 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 80256 9260337 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 80384 63076700 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 80384 38674936 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 80384 17688284 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 80512 20986652 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 80640 24401764 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 80640 18328427 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 80768 6073337 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 80896 210684017 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 80896 63695926 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 80896 24288072 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 80896 4483911 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 81024 19804161 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 81152 39407854 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 81152 20255996 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 81280 19151858 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 81408 146988091 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 81408 60307270 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 81408 25173557 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 81536 35133713 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 81664 86680821 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 81664 47645942 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 81792 39034879 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 65536 (MobiusHarmonicTree.branch 6341275950 mobiusHarmonicBlock008 mobiusHarmonicBlock009) = true := Helfgott.combined

#print axioms solution
