-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair001_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T21:52:30.975011+00:00
-- url     : https://prove2.me/submissions/7728a08c-e442-49cf-882f-8fc750155836

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16384 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16448 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 237160746 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16512 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16576 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 180009772 d11 d12
private def d6 : MobiusHarmonicTree := .branch 417170518 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16640 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16704 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 164569983 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16768 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16832 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 134830194 d18 d19
private def d13 : MobiusHarmonicTree := .branch 299400177 d14 d17
private def d5 : MobiusHarmonicTree := .branch 716570695 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16896 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 16960 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 142424715 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17024 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17088 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 163294762 d26 d27
private def d21 : MobiusHarmonicTree := .branch 305719477 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17152 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17216 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 155636553 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17280 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17344 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 127369331 d33 d34
private def d28 : MobiusHarmonicTree := .branch 283005884 d29 d32
private def d20 : MobiusHarmonicTree := .branch 588725361 d21 d28
private def d4 : MobiusHarmonicTree := .branch 1305296056 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17408 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17472 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 133892649 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17536 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17600 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 113971823 d42 d43
private def d37 : MobiusHarmonicTree := .branch 247864472 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17664 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17728 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 28763921 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17792 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17856 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 19950887 d49 d50
private def d44 : MobiusHarmonicTree := .branch 48714808 d45 d48
private def d36 : MobiusHarmonicTree := .branch 296579280 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17920 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 17984 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 56020085 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18048 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18112 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 98666027 d57 d58
private def d52 : MobiusHarmonicTree := .branch 154686112 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18176 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18240 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 127698250 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18304 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18368 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 149496545 d64 d65
private def d59 : MobiusHarmonicTree := .branch 277194795 d60 d63
private def d51 : MobiusHarmonicTree := .branch 431880907 d52 d59
private def d35 : MobiusHarmonicTree := .branch 728460187 d36 d51
private def d3 : MobiusHarmonicTree := .branch 2033756243 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18432 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18496 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 152124448 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18560 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18624 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 95474404 d74 d75
private def d69 : MobiusHarmonicTree := .branch 247598852 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18688 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18752 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 11888763 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18816 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18880 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 139260602 d81 d82
private def d76 : MobiusHarmonicTree := .branch 151149365 d77 d80
private def d68 : MobiusHarmonicTree := .branch 398748217 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 18944 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19008 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 254174994 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19072 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19136 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 294206942 d89 d90
private def d84 : MobiusHarmonicTree := .branch 548381936 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19200 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19264 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 298007885 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19328 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19392 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 278477417 d96 d97
private def d91 : MobiusHarmonicTree := .branch 576485302 d92 d95
private def d83 : MobiusHarmonicTree := .branch 1124867238 d84 d91
private def d67 : MobiusHarmonicTree := .branch 1523615455 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19456 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19520 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 194116570 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19584 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19648 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 251189740 d105 d106
private def d100 : MobiusHarmonicTree := .branch 445306310 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19712 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19776 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 295733128 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19840 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19904 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 261347219 d112 d113
private def d107 : MobiusHarmonicTree := .branch 557080347 d108 d111
private def d99 : MobiusHarmonicTree := .branch 1002386657 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 19968 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20032 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 162180015 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20096 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20160 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 148125365 d120 d121
private def d115 : MobiusHarmonicTree := .branch 310305380 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20224 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20288 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 150260468 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20352 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20416 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 151606191 d127 d128
private def d122 : MobiusHarmonicTree := .branch 301866659 d123 d126
private def d114 : MobiusHarmonicTree := .branch 612172039 d115 d122
private def d98 : MobiusHarmonicTree := .branch 1614558696 d99 d114
private def d66 : MobiusHarmonicTree := .branch 3138174151 d67 d98
private def d2 : MobiusHarmonicTree := .branch 5171930394 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20480 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20544 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 182556317 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20608 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20672 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 266486649 d138 d139
private def d133 : MobiusHarmonicTree := .branch 449042966 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20736 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20800 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 250980837 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20864 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20928 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 232871615 d145 d146
private def d140 : MobiusHarmonicTree := .branch 483852452 d141 d144
private def d132 : MobiusHarmonicTree := .branch 932895418 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 20992 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21056 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 233192638 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21120 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21184 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 194844607 d153 d154
private def d148 : MobiusHarmonicTree := .branch 428037245 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21248 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21312 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 191566817 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21376 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21440 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 145428126 d160 d161
private def d155 : MobiusHarmonicTree := .branch 336994943 d156 d159
private def d147 : MobiusHarmonicTree := .branch 765032188 d148 d155
private def d131 : MobiusHarmonicTree := .branch 1697927606 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21504 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21568 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 77526379 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21632 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21696 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 16037512 d169 d170
private def d164 : MobiusHarmonicTree := .branch 93563891 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21760 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21824 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 20801617 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21888 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 21952 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 22138500 d176 d177
private def d171 : MobiusHarmonicTree := .branch 42940117 d172 d175
private def d163 : MobiusHarmonicTree := .branch 136504008 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22016 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22080 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 68750027 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22144 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22208 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 107539053 d184 d185
private def d179 : MobiusHarmonicTree := .branch 176289080 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22272 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22336 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 114868535 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22400 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22464 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 147936378 d191 d192
private def d186 : MobiusHarmonicTree := .branch 262804913 d187 d190
private def d178 : MobiusHarmonicTree := .branch 439093993 d179 d186
private def d162 : MobiusHarmonicTree := .branch 575598001 d163 d178
private def d130 : MobiusHarmonicTree := .branch 2273525607 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22528 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22592 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 107268060 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22656 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22720 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 119940088 d201 d202
private def d196 : MobiusHarmonicTree := .branch 227208148 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22784 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22848 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 125656315 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22912 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 22976 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 133142575 d208 d209
private def d203 : MobiusHarmonicTree := .branch 258798890 d204 d207
private def d195 : MobiusHarmonicTree := .branch 486007038 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23040 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23104 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 177100957 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23168 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23232 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 172868006 d216 d217
private def d211 : MobiusHarmonicTree := .branch 349968963 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23296 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23360 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 184250336 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23424 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23488 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 163194975 d223 d224
private def d218 : MobiusHarmonicTree := .branch 347445311 d219 d222
private def d210 : MobiusHarmonicTree := .branch 697414274 d211 d218
private def d194 : MobiusHarmonicTree := .branch 1183421312 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23552 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23616 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 189419283 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23680 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23744 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 192677097 d232 d233
private def d227 : MobiusHarmonicTree := .branch 382096380 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23808 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23872 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 215937082 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 23936 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24000 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 240516776 d239 d240
private def d234 : MobiusHarmonicTree := .branch 456453858 d235 d238
private def d226 : MobiusHarmonicTree := .branch 838550238 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24064 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24128 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 331727697 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24192 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24256 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 333731385 d247 d248
private def d242 : MobiusHarmonicTree := .branch 665459082 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24320 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24384 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 280091963 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24448 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock002 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24512 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 290905522 d254 d255
private def d249 : MobiusHarmonicTree := .branch 570997485 d250 d253
private def d241 : MobiusHarmonicTree := .branch 1236456567 d242 d249
private def d225 : MobiusHarmonicTree := .branch 2075006805 d226 d241
private def d193 : MobiusHarmonicTree := .branch 3258428117 d194 d225
private def d129 : MobiusHarmonicTree := .branch 5531953724 d130 d193
private def d1 : MobiusHarmonicTree := .branch 10703884118 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24576 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24640 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 237328974 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24704 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24768 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 165997803 d266 d267
private def d261 : MobiusHarmonicTree := .branch 403326777 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24832 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24896 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 124900198 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 24960 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25024 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 91048818 d273 d274
private def d268 : MobiusHarmonicTree := .branch 215949016 d269 d272
private def d260 : MobiusHarmonicTree := .branch 619275793 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25088 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25152 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 31380985 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25216 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25280 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 24420254 d281 d282
private def d276 : MobiusHarmonicTree := .branch 55801239 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25344 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25408 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 10269649 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25472 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25536 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 35270331 d288 d289
private def d283 : MobiusHarmonicTree := .branch 45539980 d284 d287
private def d275 : MobiusHarmonicTree := .branch 101341219 d276 d283
private def d259 : MobiusHarmonicTree := .branch 720617012 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25600 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25664 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 61981300 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25728 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25792 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 62625435 d297 d298
private def d292 : MobiusHarmonicTree := .branch 124606735 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25856 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25920 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 22495780 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 25984 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26048 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 19773458 d304 d305
private def d299 : MobiusHarmonicTree := .branch 42269238 d300 d303
private def d291 : MobiusHarmonicTree := .branch 166875973 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26112 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26176 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 12560062 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26240 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26304 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 12012832 d312 d313
private def d307 : MobiusHarmonicTree := .branch 24572894 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26368 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26432 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 17825648 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26496 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26560 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 53915433 d319 d320
private def d314 : MobiusHarmonicTree := .branch 71741081 d315 d318
private def d306 : MobiusHarmonicTree := .branch 96313975 d307 d314
private def d290 : MobiusHarmonicTree := .branch 263189948 d291 d306
private def d258 : MobiusHarmonicTree := .branch 983806960 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26624 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26688 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 31979676 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26752 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26816 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 43474954 d329 d330
private def d324 : MobiusHarmonicTree := .branch 75454630 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26880 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 26944 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 62505708 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27008 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27072 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 75406385 d336 d337
private def d331 : MobiusHarmonicTree := .branch 137912093 d332 d335
private def d323 : MobiusHarmonicTree := .branch 213366723 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27136 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27200 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 43416105 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27264 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27328 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 44057514 d344 d345
private def d339 : MobiusHarmonicTree := .branch 87473619 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27392 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27456 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 31813716 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27520 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27584 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 66904708 d351 d352
private def d346 : MobiusHarmonicTree := .branch 98718424 d347 d350
private def d338 : MobiusHarmonicTree := .branch 186192043 d339 d346
private def d322 : MobiusHarmonicTree := .branch 399558766 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27648 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27712 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 77930095 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27776 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27840 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 55678461 d360 d361
private def d355 : MobiusHarmonicTree := .branch 133608556 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27904 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 27968 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 12234027 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28032 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28096 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 18404403 d367 d368
private def d362 : MobiusHarmonicTree := .branch 30638430 d363 d366
private def d354 : MobiusHarmonicTree := .branch 164246986 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28160 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28224 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 9670868 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28288 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28352 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 31524008 d375 d376
private def d370 : MobiusHarmonicTree := .branch 41194876 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28416 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28480 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 32131197 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28544 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28608 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 24976337 d382 d383
private def d377 : MobiusHarmonicTree := .branch 57107534 d378 d381
private def d369 : MobiusHarmonicTree := .branch 98302410 d370 d377
private def d353 : MobiusHarmonicTree := .branch 262549396 d354 d369
private def d321 : MobiusHarmonicTree := .branch 662108162 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1645915122 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28672 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28736 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 71174478 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28800 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28864 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 104770078 d393 d394
private def d388 : MobiusHarmonicTree := .branch 175944556 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28928 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 28992 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 91577878 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29056 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29120 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 38904512 d400 d401
private def d395 : MobiusHarmonicTree := .branch 130482390 d396 d399
private def d387 : MobiusHarmonicTree := .branch 306426946 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29184 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29248 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 49716308 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29312 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29376 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 29853228 d408 d409
private def d403 : MobiusHarmonicTree := .branch 79569536 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29440 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29504 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 39596222 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29568 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29632 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 62658069 d415 d416
private def d410 : MobiusHarmonicTree := .branch 102254291 d411 d414
private def d402 : MobiusHarmonicTree := .branch 181823827 d403 d410
private def d386 : MobiusHarmonicTree := .branch 488250773 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29696 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29760 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 98643950 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29824 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29888 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 119976801 d424 d425
private def d419 : MobiusHarmonicTree := .branch 218620751 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 29952 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30016 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 80966148 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30080 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30144 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 40884604 d431 d432
private def d426 : MobiusHarmonicTree := .branch 121850752 d427 d430
private def d418 : MobiusHarmonicTree := .branch 340471503 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30208 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30272 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 17798871 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30336 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30400 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 58527423 d439 d440
private def d434 : MobiusHarmonicTree := .branch 76326294 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30464 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30528 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 111329142 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30592 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30656 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 145101324 d446 d447
private def d441 : MobiusHarmonicTree := .branch 256430466 d442 d445
private def d433 : MobiusHarmonicTree := .branch 332756760 d434 d441
private def d417 : MobiusHarmonicTree := .branch 673228263 d418 d433
private def d385 : MobiusHarmonicTree := .branch 1161479036 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30720 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30784 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 169132840 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30848 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30912 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 169741640 d456 d457
private def d451 : MobiusHarmonicTree := .branch 338874480 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 30976 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31040 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 187591805 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31104 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31168 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 183568651 d463 d464
private def d458 : MobiusHarmonicTree := .branch 371160456 d459 d462
private def d450 : MobiusHarmonicTree := .branch 710034936 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31232 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31296 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 145639058 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31360 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31424 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 154817651 d471 d472
private def d466 : MobiusHarmonicTree := .branch 300456709 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31488 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31552 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 197987984 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31616 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31680 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 211952287 d478 d479
private def d473 : MobiusHarmonicTree := .branch 409940271 d474 d477
private def d465 : MobiusHarmonicTree := .branch 710396980 d466 d473
private def d449 : MobiusHarmonicTree := .branch 1420431916 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31744 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31808 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 211933320 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31872 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 31936 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 259474504 d487 d488
private def d482 : MobiusHarmonicTree := .branch 471407824 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32000 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32064 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 231935435 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32128 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32192 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 219909901 d494 d495
private def d489 : MobiusHarmonicTree := .branch 451845336 d490 d493
private def d481 : MobiusHarmonicTree := .branch 923253160 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32256 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32320 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 200392474 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32384 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32448 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 156360711 d502 d503
private def d497 : MobiusHarmonicTree := .branch 356753185 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32512 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32576 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 110771931 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32640 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock003 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 32704 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 92524805 d509 d510
private def d504 : MobiusHarmonicTree := .branch 203296736 d505 d508
private def d496 : MobiusHarmonicTree := .branch 560049921 d497 d504
private def d480 : MobiusHarmonicTree := .branch 1483303081 d481 d496
private def d448 : MobiusHarmonicTree := .branch 2903734997 d449 d480
private def d384 : MobiusHarmonicTree := .branch 4065214033 d385 d448
private def d256 : MobiusHarmonicTree := .branch 5711129155 d257 d384
private def d0 : MobiusHarmonicTree := .branch 16415013273 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 16384 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 16384 16415013273 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 16384 10703884118 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 16384 5171930394 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 16384 2033756243 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 16384 1305296056 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 16384 716570695 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 16384 417170518 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 16384 237160746 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 16512 180009772 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 16640 299400177 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 16640 164569983 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 16768 134830194 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 16896 588725361 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 16896 305719477 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 16896 142424715 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 17024 163294762 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 17152 283005884 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 17152 155636553 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 17280 127369331 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 17408 728460187 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 17408 296579280 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 17408 247864472 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 17408 133892649 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 17536 113971823 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 17664 48714808 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 17664 28763921 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 17792 19950887 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 17920 431880907 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 17920 154686112 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 17920 56020085 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 18048 98666027 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 18176 277194795 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 18176 127698250 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 18304 149496545 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 18432 3138174151 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 18432 1523615455 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 18432 398748217 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 18432 247598852 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 18432 152124448 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 18560 95474404 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 18688 151149365 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 18688 11888763 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 18816 139260602 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 18944 1124867238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 18944 548381936 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 18944 254174994 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 19072 294206942 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 19200 576485302 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 19200 298007885 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 19328 278477417 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 19456 1614558696 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 19456 1002386657 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 19456 445306310 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 19456 194116570 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 19584 251189740 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 19712 557080347 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 19712 295733128 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 19840 261347219 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 19968 612172039 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 19968 310305380 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 19968 162180015 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 20096 148125365 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 20224 301866659 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 20224 150260468 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 20352 151606191 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 20480 5531953724 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 20480 2273525607 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 20480 1697927606 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 20480 932895418 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 20480 449042966 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 20480 182556317 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 20608 266486649 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 20736 483852452 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 20736 250980837 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 20864 232871615 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 20992 765032188 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 20992 428037245 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 20992 233192638 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 21120 194844607 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 21248 336994943 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 21248 191566817 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 21376 145428126 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 21504 575598001 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 21504 136504008 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 21504 93563891 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 21504 77526379 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 21632 16037512 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 21760 42940117 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 21760 20801617 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 21888 22138500 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 22016 439093993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 22016 176289080 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 22016 68750027 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 22144 107539053 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 22272 262804913 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 22272 114868535 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 22400 147936378 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 22528 3258428117 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 22528 1183421312 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 22528 486007038 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 22528 227208148 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 22528 107268060 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 22656 119940088 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 22784 258798890 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 22784 125656315 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 22912 133142575 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 23040 697414274 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 23040 349968963 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 23040 177100957 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 23168 172868006 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 23296 347445311 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 23296 184250336 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 23424 163194975 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 23552 2075006805 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 23552 838550238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 23552 382096380 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 23552 189419283 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 23680 192677097 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 23808 456453858 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 23808 215937082 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 23936 240516776 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 24064 1236456567 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 24064 665459082 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 24064 331727697 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 24192 333731385 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 24320 570997485 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 24320 280091963 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 24448 290905522 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 24576 5711129155 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 24576 1645915122 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 24576 983806960 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 24576 720617012 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 24576 619275793 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 24576 403326777 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 24576 237328974 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 24704 165997803 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 24832 215949016 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 24832 124900198 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 24960 91048818 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 25088 101341219 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 25088 55801239 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 25088 31380985 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 25216 24420254 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 25344 45539980 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 25344 10269649 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 25472 35270331 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 25600 263189948 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 25600 166875973 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 25600 124606735 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 25600 61981300 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 25728 62625435 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 25856 42269238 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 25856 22495780 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 25984 19773458 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 26112 96313975 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 26112 24572894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 26112 12560062 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 26240 12012832 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 26368 71741081 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 26368 17825648 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 26496 53915433 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 26624 662108162 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 26624 399558766 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 26624 213366723 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 26624 75454630 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 26624 31979676 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 26752 43474954 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 26880 137912093 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 26880 62505708 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 27008 75406385 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 27136 186192043 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 27136 87473619 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 27136 43416105 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 27264 44057514 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 27392 98718424 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 27392 31813716 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 27520 66904708 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 27648 262549396 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 27648 164246986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 27648 133608556 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 27648 77930095 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 27776 55678461 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 27904 30638430 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 27904 12234027 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 28032 18404403 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 28160 98302410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 28160 41194876 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 28160 9670868 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 28288 31524008 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 28416 57107534 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 28416 32131197 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 28544 24976337 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 28672 4065214033 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 28672 1161479036 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 28672 488250773 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 28672 306426946 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 28672 175944556 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 28672 71174478 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 28800 104770078 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 28928 130482390 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 28928 91577878 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 29056 38904512 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 29184 181823827 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 29184 79569536 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 29184 49716308 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 29312 29853228 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 29440 102254291 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 29440 39596222 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 29568 62658069 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 29696 673228263 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 29696 340471503 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 29696 218620751 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 29696 98643950 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 29824 119976801 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 29952 121850752 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 29952 80966148 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 30080 40884604 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 30208 332756760 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 30208 76326294 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 30208 17798871 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 30336 58527423 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 30464 256430466 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 30464 111329142 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 30592 145101324 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 30720 2903734997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 30720 1420431916 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 30720 710034936 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 30720 338874480 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 30720 169132840 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 30848 169741640 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 30976 371160456 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 30976 187591805 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 31104 183568651 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 31232 710396980 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 31232 300456709 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 31232 145639058 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 31360 154817651 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 31488 409940271 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 31488 197987984 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 31616 211952287 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 31744 1483303081 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 31744 923253160 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 31744 471407824 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 31744 211933320 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 31872 259474504 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 32000 451845336 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 32000 231935435 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 32128 219909901 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 32256 560049921 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 32256 356753185 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 32256 200392474 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 32384 156360711 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 32512 203296736 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 32512 110771931 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 32640 92524805 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 16384 (MobiusHarmonicTree.branch 16415013273 mobiusHarmonicBlock002 mobiusHarmonicBlock003) = true := Helfgott.combined

#print axioms solution
