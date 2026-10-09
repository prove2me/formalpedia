-- Prove2me | solution 1 for Helfgott.mobiusHarmonicPair013_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-08T22:39:48.537351+00:00
-- url     : https://prove2.me/submissions/11e3dc3a-2de4-467c-94e3-d2c342ac046b

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

private abbrev d8 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 0
private theorem p8 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 212992 d8 = true := by decide +kernel

private abbrev d9 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 1
private theorem p9 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213056 d9 = true := by decide +kernel

private def d7 : MobiusHarmonicTree := .branch 15873730 d8 d9
private abbrev d11 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 2
private theorem p11 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213120 d11 = true := by decide +kernel

private abbrev d12 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 3
private theorem p12 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213184 d12 = true := by decide +kernel

private def d10 : MobiusHarmonicTree := .branch 20582791 d11 d12
private def d6 : MobiusHarmonicTree := .branch 36456521 d7 d10
private abbrev d15 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 4
private theorem p15 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213248 d15 = true := by decide +kernel

private abbrev d16 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 5
private theorem p16 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213312 d16 = true := by decide +kernel

private def d14 : MobiusHarmonicTree := .branch 22544521 d15 d16
private abbrev d18 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 6
private theorem p18 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213376 d18 = true := by decide +kernel

private abbrev d19 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 7
private theorem p19 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213440 d19 = true := by decide +kernel

private def d17 : MobiusHarmonicTree := .branch 18493041 d18 d19
private def d13 : MobiusHarmonicTree := .branch 41037562 d14 d17
private def d5 : MobiusHarmonicTree := .branch 77494083 d6 d13
private abbrev d23 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 8
private theorem p23 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213504 d23 = true := by decide +kernel

private abbrev d24 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 9
private theorem p24 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213568 d24 = true := by decide +kernel

private def d22 : MobiusHarmonicTree := .branch 7983726 d23 d24
private abbrev d26 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 10
private theorem p26 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213632 d26 = true := by decide +kernel

private abbrev d27 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 11
private theorem p27 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213696 d27 = true := by decide +kernel

private def d25 : MobiusHarmonicTree := .branch 7875729 d26 d27
private def d21 : MobiusHarmonicTree := .branch 15859455 d22 d25
private abbrev d30 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 12
private theorem p30 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213760 d30 = true := by decide +kernel

private abbrev d31 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 13
private theorem p31 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213824 d31 = true := by decide +kernel

private def d29 : MobiusHarmonicTree := .branch 4906147 d30 d31
private abbrev d33 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 14
private theorem p33 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213888 d33 = true := by decide +kernel

private abbrev d34 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 15
private theorem p34 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 213952 d34 = true := by decide +kernel

private def d32 : MobiusHarmonicTree := .branch 2444327 d33 d34
private def d28 : MobiusHarmonicTree := .branch 7350474 d29 d32
private def d20 : MobiusHarmonicTree := .branch 23209929 d21 d28
private def d4 : MobiusHarmonicTree := .branch 100704012 d5 d20
private abbrev d39 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 16
private theorem p39 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214016 d39 = true := by decide +kernel

private abbrev d40 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 17
private theorem p40 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214080 d40 = true := by decide +kernel

private def d38 : MobiusHarmonicTree := .branch 6296977 d39 d40
private abbrev d42 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 18
private theorem p42 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214144 d42 = true := by decide +kernel

private abbrev d43 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 19
private theorem p43 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214208 d43 = true := by decide +kernel

private def d41 : MobiusHarmonicTree := .branch 989813 d42 d43
private def d37 : MobiusHarmonicTree := .branch 7286790 d38 d41
private abbrev d46 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 20
private theorem p46 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214272 d46 = true := by decide +kernel

private abbrev d47 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 21
private theorem p47 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214336 d47 = true := by decide +kernel

private def d45 : MobiusHarmonicTree := .branch 1217757 d46 d47
private abbrev d49 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 22
private theorem p49 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214400 d49 = true := by decide +kernel

private abbrev d50 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 23
private theorem p50 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214464 d50 = true := by decide +kernel

private def d48 : MobiusHarmonicTree := .branch 3231150 d49 d50
private def d44 : MobiusHarmonicTree := .branch 4448907 d45 d48
private def d36 : MobiusHarmonicTree := .branch 11735697 d37 d44
private abbrev d54 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 24
private theorem p54 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214528 d54 = true := by decide +kernel

private abbrev d55 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 25
private theorem p55 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214592 d55 = true := by decide +kernel

private def d53 : MobiusHarmonicTree := .branch 3429826 d54 d55
private abbrev d57 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 26
private theorem p57 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214656 d57 = true := by decide +kernel

private abbrev d58 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 27
private theorem p58 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214720 d58 = true := by decide +kernel

private def d56 : MobiusHarmonicTree := .branch 3791218 d57 d58
private def d52 : MobiusHarmonicTree := .branch 7221044 d53 d56
private abbrev d61 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 28
private theorem p61 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214784 d61 = true := by decide +kernel

private abbrev d62 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 29
private theorem p62 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214848 d62 = true := by decide +kernel

private def d60 : MobiusHarmonicTree := .branch 2866989 d61 d62
private abbrev d64 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 30
private theorem p64 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214912 d64 = true := by decide +kernel

private abbrev d65 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 31
private theorem p65 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 214976 d65 = true := by decide +kernel

private def d63 : MobiusHarmonicTree := .branch 4758960 d64 d65
private def d59 : MobiusHarmonicTree := .branch 7625949 d60 d63
private def d51 : MobiusHarmonicTree := .branch 14846993 d52 d59
private def d35 : MobiusHarmonicTree := .branch 26582690 d36 d51
private def d3 : MobiusHarmonicTree := .branch 127286702 d4 d35
private abbrev d71 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 32
private theorem p71 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215040 d71 = true := by decide +kernel

private abbrev d72 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 33
private theorem p72 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215104 d72 = true := by decide +kernel

private def d70 : MobiusHarmonicTree := .branch 5327678 d71 d72
private abbrev d74 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 34
private theorem p74 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215168 d74 = true := by decide +kernel

private abbrev d75 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 35
private theorem p75 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215232 d75 = true := by decide +kernel

private def d73 : MobiusHarmonicTree := .branch 15387732 d74 d75
private def d69 : MobiusHarmonicTree := .branch 20715410 d70 d73
private abbrev d78 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 36
private theorem p78 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215296 d78 = true := by decide +kernel

private abbrev d79 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 37
private theorem p79 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215360 d79 = true := by decide +kernel

private def d77 : MobiusHarmonicTree := .branch 18680353 d78 d79
private abbrev d81 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 38
private theorem p81 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215424 d81 = true := by decide +kernel

private abbrev d82 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 39
private theorem p82 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215488 d82 = true := by decide +kernel

private def d80 : MobiusHarmonicTree := .branch 18274883 d81 d82
private def d76 : MobiusHarmonicTree := .branch 36955236 d77 d80
private def d68 : MobiusHarmonicTree := .branch 57670646 d69 d76
private abbrev d86 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 40
private theorem p86 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215552 d86 = true := by decide +kernel

private abbrev d87 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 41
private theorem p87 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215616 d87 = true := by decide +kernel

private def d85 : MobiusHarmonicTree := .branch 12643544 d86 d87
private abbrev d89 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 42
private theorem p89 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215680 d89 = true := by decide +kernel

private abbrev d90 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 43
private theorem p90 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215744 d90 = true := by decide +kernel

private def d88 : MobiusHarmonicTree := .branch 6878648 d89 d90
private def d84 : MobiusHarmonicTree := .branch 19522192 d85 d88
private abbrev d93 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 44
private theorem p93 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215808 d93 = true := by decide +kernel

private abbrev d94 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 45
private theorem p94 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215872 d94 = true := by decide +kernel

private def d92 : MobiusHarmonicTree := .branch 5123538 d93 d94
private abbrev d96 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 46
private theorem p96 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 215936 d96 = true := by decide +kernel

private abbrev d97 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 47
private theorem p97 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216000 d97 = true := by decide +kernel

private def d95 : MobiusHarmonicTree := .branch 12735964 d96 d97
private def d91 : MobiusHarmonicTree := .branch 17859502 d92 d95
private def d83 : MobiusHarmonicTree := .branch 37381694 d84 d91
private def d67 : MobiusHarmonicTree := .branch 95052340 d68 d83
private abbrev d102 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 48
private theorem p102 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216064 d102 = true := by decide +kernel

private abbrev d103 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 49
private theorem p103 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216128 d103 = true := by decide +kernel

private def d101 : MobiusHarmonicTree := .branch 18845109 d102 d103
private abbrev d105 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 50
private theorem p105 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216192 d105 = true := by decide +kernel

private abbrev d106 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 51
private theorem p106 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216256 d106 = true := by decide +kernel

private def d104 : MobiusHarmonicTree := .branch 19319952 d105 d106
private def d100 : MobiusHarmonicTree := .branch 38165061 d101 d104
private abbrev d109 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 52
private theorem p109 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216320 d109 = true := by decide +kernel

private abbrev d110 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 53
private theorem p110 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216384 d110 = true := by decide +kernel

private def d108 : MobiusHarmonicTree := .branch 19363575 d109 d110
private abbrev d112 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 54
private theorem p112 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216448 d112 = true := by decide +kernel

private abbrev d113 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 55
private theorem p113 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216512 d113 = true := by decide +kernel

private def d111 : MobiusHarmonicTree := .branch 16826330 d112 d113
private def d107 : MobiusHarmonicTree := .branch 36189905 d108 d111
private def d99 : MobiusHarmonicTree := .branch 74354966 d100 d107
private abbrev d117 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 56
private theorem p117 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216576 d117 = true := by decide +kernel

private abbrev d118 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 57
private theorem p118 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216640 d118 = true := by decide +kernel

private def d116 : MobiusHarmonicTree := .branch 10898215 d117 d118
private abbrev d120 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 58
private theorem p120 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216704 d120 = true := by decide +kernel

private abbrev d121 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 59
private theorem p121 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216768 d121 = true := by decide +kernel

private def d119 : MobiusHarmonicTree := .branch 11352991 d120 d121
private def d115 : MobiusHarmonicTree := .branch 22251206 d116 d119
private abbrev d124 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 60
private theorem p124 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216832 d124 = true := by decide +kernel

private abbrev d125 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 61
private theorem p125 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216896 d125 = true := by decide +kernel

private def d123 : MobiusHarmonicTree := .branch 12227251 d124 d125
private abbrev d127 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 62
private theorem p127 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 216960 d127 = true := by decide +kernel

private abbrev d128 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 63
private theorem p128 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217024 d128 = true := by decide +kernel

private def d126 : MobiusHarmonicTree := .branch 13063324 d127 d128
private def d122 : MobiusHarmonicTree := .branch 25290575 d123 d126
private def d114 : MobiusHarmonicTree := .branch 47541781 d115 d122
private def d98 : MobiusHarmonicTree := .branch 121896747 d99 d114
private def d66 : MobiusHarmonicTree := .branch 216949087 d67 d98
private def d2 : MobiusHarmonicTree := .branch 344235789 d3 d66
private abbrev d135 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 64
private theorem p135 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217088 d135 = true := by decide +kernel

private abbrev d136 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 65
private theorem p136 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217152 d136 = true := by decide +kernel

private def d134 : MobiusHarmonicTree := .branch 7349880 d135 d136
private abbrev d138 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 66
private theorem p138 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217216 d138 = true := by decide +kernel

private abbrev d139 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 67
private theorem p139 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217280 d139 = true := by decide +kernel

private def d137 : MobiusHarmonicTree := .branch 10162036 d138 d139
private def d133 : MobiusHarmonicTree := .branch 17511916 d134 d137
private abbrev d142 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 68
private theorem p142 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217344 d142 = true := by decide +kernel

private abbrev d143 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 69
private theorem p143 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217408 d143 = true := by decide +kernel

private def d141 : MobiusHarmonicTree := .branch 19028759 d142 d143
private abbrev d145 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 70
private theorem p145 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217472 d145 = true := by decide +kernel

private abbrev d146 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 71
private theorem p146 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217536 d146 = true := by decide +kernel

private def d144 : MobiusHarmonicTree := .branch 19918584 d145 d146
private def d140 : MobiusHarmonicTree := .branch 38947343 d141 d144
private def d132 : MobiusHarmonicTree := .branch 56459259 d133 d140
private abbrev d150 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 72
private theorem p150 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217600 d150 = true := by decide +kernel

private abbrev d151 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 73
private theorem p151 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217664 d151 = true := by decide +kernel

private def d149 : MobiusHarmonicTree := .branch 15395505 d150 d151
private abbrev d153 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 74
private theorem p153 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217728 d153 = true := by decide +kernel

private abbrev d154 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 75
private theorem p154 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217792 d154 = true := by decide +kernel

private def d152 : MobiusHarmonicTree := .branch 16235764 d153 d154
private def d148 : MobiusHarmonicTree := .branch 31631269 d149 d152
private abbrev d157 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 76
private theorem p157 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217856 d157 = true := by decide +kernel

private abbrev d158 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 77
private theorem p158 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217920 d158 = true := by decide +kernel

private def d156 : MobiusHarmonicTree := .branch 8168752 d157 d158
private abbrev d160 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 78
private theorem p160 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 217984 d160 = true := by decide +kernel

private abbrev d161 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 79
private theorem p161 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218048 d161 = true := by decide +kernel

private def d159 : MobiusHarmonicTree := .branch 3737432 d160 d161
private def d155 : MobiusHarmonicTree := .branch 11906184 d156 d159
private def d147 : MobiusHarmonicTree := .branch 43537453 d148 d155
private def d131 : MobiusHarmonicTree := .branch 99996712 d132 d147
private abbrev d166 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 80
private theorem p166 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218112 d166 = true := by decide +kernel

private abbrev d167 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 81
private theorem p167 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218176 d167 = true := by decide +kernel

private def d165 : MobiusHarmonicTree := .branch 9721512 d166 d167
private abbrev d169 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 82
private theorem p169 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218240 d169 = true := by decide +kernel

private abbrev d170 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 83
private theorem p170 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218304 d170 = true := by decide +kernel

private def d168 : MobiusHarmonicTree := .branch 3628433 d169 d170
private def d164 : MobiusHarmonicTree := .branch 13349945 d165 d168
private abbrev d173 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 84
private theorem p173 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218368 d173 = true := by decide +kernel

private abbrev d174 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 85
private theorem p174 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218432 d174 = true := by decide +kernel

private def d172 : MobiusHarmonicTree := .branch 3025915 d173 d174
private abbrev d176 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 86
private theorem p176 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218496 d176 = true := by decide +kernel

private abbrev d177 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 87
private theorem p177 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218560 d177 = true := by decide +kernel

private def d175 : MobiusHarmonicTree := .branch 4543786 d176 d177
private def d171 : MobiusHarmonicTree := .branch 7569701 d172 d175
private def d163 : MobiusHarmonicTree := .branch 20919646 d164 d171
private abbrev d181 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 88
private theorem p181 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218624 d181 = true := by decide +kernel

private abbrev d182 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 89
private theorem p182 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218688 d182 = true := by decide +kernel

private def d180 : MobiusHarmonicTree := .branch 3264843 d181 d182
private abbrev d184 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 90
private theorem p184 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218752 d184 = true := by decide +kernel

private abbrev d185 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 91
private theorem p185 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218816 d185 = true := by decide +kernel

private def d183 : MobiusHarmonicTree := .branch 3495935 d184 d185
private def d179 : MobiusHarmonicTree := .branch 6760778 d180 d183
private abbrev d188 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 92
private theorem p188 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218880 d188 = true := by decide +kernel

private abbrev d189 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 93
private theorem p189 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 218944 d189 = true := by decide +kernel

private def d187 : MobiusHarmonicTree := .branch 6147869 d188 d189
private abbrev d191 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 94
private theorem p191 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219008 d191 = true := by decide +kernel

private abbrev d192 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 95
private theorem p192 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219072 d192 = true := by decide +kernel

private def d190 : MobiusHarmonicTree := .branch 1711712 d191 d192
private def d186 : MobiusHarmonicTree := .branch 7859581 d187 d190
private def d178 : MobiusHarmonicTree := .branch 14620359 d179 d186
private def d162 : MobiusHarmonicTree := .branch 35540005 d163 d178
private def d130 : MobiusHarmonicTree := .branch 135536717 d131 d162
private abbrev d198 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 96
private theorem p198 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219136 d198 = true := by decide +kernel

private abbrev d199 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 97
private theorem p199 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219200 d199 = true := by decide +kernel

private def d197 : MobiusHarmonicTree := .branch 1031070 d198 d199
private abbrev d201 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 98
private theorem p201 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219264 d201 = true := by decide +kernel

private abbrev d202 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 99
private theorem p202 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219328 d202 = true := by decide +kernel

private def d200 : MobiusHarmonicTree := .branch 2785684 d201 d202
private def d196 : MobiusHarmonicTree := .branch 3816754 d197 d200
private abbrev d205 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 100
private theorem p205 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219392 d205 = true := by decide +kernel

private abbrev d206 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 101
private theorem p206 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219456 d206 = true := by decide +kernel

private def d204 : MobiusHarmonicTree := .branch 5463618 d205 d206
private abbrev d208 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 102
private theorem p208 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219520 d208 = true := by decide +kernel

private abbrev d209 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 103
private theorem p209 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219584 d209 = true := by decide +kernel

private def d207 : MobiusHarmonicTree := .branch 12154522 d208 d209
private def d203 : MobiusHarmonicTree := .branch 17618140 d204 d207
private def d195 : MobiusHarmonicTree := .branch 21434894 d196 d203
private abbrev d213 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 104
private theorem p213 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219648 d213 = true := by decide +kernel

private abbrev d214 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 105
private theorem p214 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219712 d214 = true := by decide +kernel

private def d212 : MobiusHarmonicTree := .branch 13836585 d213 d214
private abbrev d216 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 106
private theorem p216 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219776 d216 = true := by decide +kernel

private abbrev d217 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 107
private theorem p217 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219840 d217 = true := by decide +kernel

private def d215 : MobiusHarmonicTree := .branch 14519544 d216 d217
private def d211 : MobiusHarmonicTree := .branch 28356129 d212 d215
private abbrev d220 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 108
private theorem p220 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219904 d220 = true := by decide +kernel

private abbrev d221 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 109
private theorem p221 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 219968 d221 = true := by decide +kernel

private def d219 : MobiusHarmonicTree := .branch 16297530 d220 d221
private abbrev d223 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 110
private theorem p223 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220032 d223 = true := by decide +kernel

private abbrev d224 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 111
private theorem p224 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220096 d224 = true := by decide +kernel

private def d222 : MobiusHarmonicTree := .branch 17593214 d223 d224
private def d218 : MobiusHarmonicTree := .branch 33890744 d219 d222
private def d210 : MobiusHarmonicTree := .branch 62246873 d211 d218
private def d194 : MobiusHarmonicTree := .branch 83681767 d195 d210
private abbrev d229 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 112
private theorem p229 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220160 d229 = true := by decide +kernel

private abbrev d230 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 113
private theorem p230 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220224 d230 = true := by decide +kernel

private def d228 : MobiusHarmonicTree := .branch 16991501 d229 d230
private abbrev d232 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 114
private theorem p232 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220288 d232 = true := by decide +kernel

private abbrev d233 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 115
private theorem p233 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220352 d233 = true := by decide +kernel

private def d231 : MobiusHarmonicTree := .branch 22305219 d232 d233
private def d227 : MobiusHarmonicTree := .branch 39296720 d228 d231
private abbrev d236 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 116
private theorem p236 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220416 d236 = true := by decide +kernel

private abbrev d237 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 117
private theorem p237 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220480 d237 = true := by decide +kernel

private def d235 : MobiusHarmonicTree := .branch 24655425 d236 d237
private abbrev d239 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 118
private theorem p239 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220544 d239 = true := by decide +kernel

private abbrev d240 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 119
private theorem p240 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220608 d240 = true := by decide +kernel

private def d238 : MobiusHarmonicTree := .branch 24074506 d239 d240
private def d234 : MobiusHarmonicTree := .branch 48729931 d235 d238
private def d226 : MobiusHarmonicTree := .branch 88026651 d227 d234
private abbrev d244 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 120
private theorem p244 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220672 d244 = true := by decide +kernel

private abbrev d245 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 121
private theorem p245 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220736 d245 = true := by decide +kernel

private def d243 : MobiusHarmonicTree := .branch 25315445 d244 d245
private abbrev d247 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 122
private theorem p247 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220800 d247 = true := by decide +kernel

private abbrev d248 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 123
private theorem p248 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220864 d248 = true := by decide +kernel

private def d246 : MobiusHarmonicTree := .branch 29357199 d247 d248
private def d242 : MobiusHarmonicTree := .branch 54672644 d243 d246
private abbrev d251 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 124
private theorem p251 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220928 d251 = true := by decide +kernel

private abbrev d252 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 125
private theorem p252 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 220992 d252 = true := by decide +kernel

private def d250 : MobiusHarmonicTree := .branch 29340936 d251 d252
private abbrev d254 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 126
private theorem p254 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221056 d254 = true := by decide +kernel

private abbrev d255 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock026 127
private theorem p255 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221120 d255 = true := by decide +kernel

private def d253 : MobiusHarmonicTree := .branch 28116243 d254 d255
private def d249 : MobiusHarmonicTree := .branch 57457179 d250 d253
private def d241 : MobiusHarmonicTree := .branch 112129823 d242 d249
private def d225 : MobiusHarmonicTree := .branch 200156474 d226 d241
private def d193 : MobiusHarmonicTree := .branch 283838241 d194 d225
private def d129 : MobiusHarmonicTree := .branch 419374958 d130 d193
private def d1 : MobiusHarmonicTree := .branch 763610747 d2 d129
private abbrev d263 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 0
private theorem p263 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221184 d263 = true := by decide +kernel

private abbrev d264 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 1
private theorem p264 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221248 d264 = true := by decide +kernel

private def d262 : MobiusHarmonicTree := .branch 27412786 d263 d264
private abbrev d266 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 2
private theorem p266 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221312 d266 = true := by decide +kernel

private abbrev d267 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 3
private theorem p267 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221376 d267 = true := by decide +kernel

private def d265 : MobiusHarmonicTree := .branch 27627304 d266 d267
private def d261 : MobiusHarmonicTree := .branch 55040090 d262 d265
private abbrev d270 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 4
private theorem p270 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221440 d270 = true := by decide +kernel

private abbrev d271 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 5
private theorem p271 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221504 d271 = true := by decide +kernel

private def d269 : MobiusHarmonicTree := .branch 34021795 d270 d271
private abbrev d273 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 6
private theorem p273 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221568 d273 = true := by decide +kernel

private abbrev d274 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 7
private theorem p274 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221632 d274 = true := by decide +kernel

private def d272 : MobiusHarmonicTree := .branch 39561212 d273 d274
private def d268 : MobiusHarmonicTree := .branch 73583007 d269 d272
private def d260 : MobiusHarmonicTree := .branch 128623097 d261 d268
private abbrev d278 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 8
private theorem p278 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221696 d278 = true := by decide +kernel

private abbrev d279 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 9
private theorem p279 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221760 d279 = true := by decide +kernel

private def d277 : MobiusHarmonicTree := .branch 45305802 d278 d279
private abbrev d281 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 10
private theorem p281 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221824 d281 = true := by decide +kernel

private abbrev d282 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 11
private theorem p282 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221888 d282 = true := by decide +kernel

private def d280 : MobiusHarmonicTree := .branch 37050769 d281 d282
private def d276 : MobiusHarmonicTree := .branch 82356571 d277 d280
private abbrev d285 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 12
private theorem p285 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 221952 d285 = true := by decide +kernel

private abbrev d286 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 13
private theorem p286 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222016 d286 = true := by decide +kernel

private def d284 : MobiusHarmonicTree := .branch 38568950 d285 d286
private abbrev d288 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 14
private theorem p288 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222080 d288 = true := by decide +kernel

private abbrev d289 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 15
private theorem p289 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222144 d289 = true := by decide +kernel

private def d287 : MobiusHarmonicTree := .branch 43467131 d288 d289
private def d283 : MobiusHarmonicTree := .branch 82036081 d284 d287
private def d275 : MobiusHarmonicTree := .branch 164392652 d276 d283
private def d259 : MobiusHarmonicTree := .branch 293015749 d260 d275
private abbrev d294 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 16
private theorem p294 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222208 d294 = true := by decide +kernel

private abbrev d295 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 17
private theorem p295 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222272 d295 = true := by decide +kernel

private def d293 : MobiusHarmonicTree := .branch 43284911 d294 d295
private abbrev d297 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 18
private theorem p297 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222336 d297 = true := by decide +kernel

private abbrev d298 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 19
private theorem p298 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222400 d298 = true := by decide +kernel

private def d296 : MobiusHarmonicTree := .branch 49964385 d297 d298
private def d292 : MobiusHarmonicTree := .branch 93249296 d293 d296
private abbrev d301 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 20
private theorem p301 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222464 d301 = true := by decide +kernel

private abbrev d302 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 21
private theorem p302 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222528 d302 = true := by decide +kernel

private def d300 : MobiusHarmonicTree := .branch 46619335 d301 d302
private abbrev d304 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 22
private theorem p304 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222592 d304 = true := by decide +kernel

private abbrev d305 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 23
private theorem p305 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222656 d305 = true := by decide +kernel

private def d303 : MobiusHarmonicTree := .branch 41966369 d304 d305
private def d299 : MobiusHarmonicTree := .branch 88585704 d300 d303
private def d291 : MobiusHarmonicTree := .branch 181835000 d292 d299
private abbrev d309 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 24
private theorem p309 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222720 d309 = true := by decide +kernel

private abbrev d310 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 25
private theorem p310 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222784 d310 = true := by decide +kernel

private def d308 : MobiusHarmonicTree := .branch 41713013 d309 d310
private abbrev d312 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 26
private theorem p312 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222848 d312 = true := by decide +kernel

private abbrev d313 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 27
private theorem p313 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222912 d313 = true := by decide +kernel

private def d311 : MobiusHarmonicTree := .branch 44946150 d312 d313
private def d307 : MobiusHarmonicTree := .branch 86659163 d308 d311
private abbrev d316 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 28
private theorem p316 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 222976 d316 = true := by decide +kernel

private abbrev d317 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 29
private theorem p317 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223040 d317 = true := by decide +kernel

private def d315 : MobiusHarmonicTree := .branch 44131044 d316 d317
private abbrev d319 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 30
private theorem p319 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223104 d319 = true := by decide +kernel

private abbrev d320 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 31
private theorem p320 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223168 d320 = true := by decide +kernel

private def d318 : MobiusHarmonicTree := .branch 46704981 d319 d320
private def d314 : MobiusHarmonicTree := .branch 90836025 d315 d318
private def d306 : MobiusHarmonicTree := .branch 177495188 d307 d314
private def d290 : MobiusHarmonicTree := .branch 359330188 d291 d306
private def d258 : MobiusHarmonicTree := .branch 652345937 d259 d290
private abbrev d326 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 32
private theorem p326 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223232 d326 = true := by decide +kernel

private abbrev d327 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 33
private theorem p327 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223296 d327 = true := by decide +kernel

private def d325 : MobiusHarmonicTree := .branch 48612526 d326 d327
private abbrev d329 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 34
private theorem p329 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223360 d329 = true := by decide +kernel

private abbrev d330 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 35
private theorem p330 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223424 d330 = true := by decide +kernel

private def d328 : MobiusHarmonicTree := .branch 50957077 d329 d330
private def d324 : MobiusHarmonicTree := .branch 99569603 d325 d328
private abbrev d333 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 36
private theorem p333 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223488 d333 = true := by decide +kernel

private abbrev d334 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 37
private theorem p334 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223552 d334 = true := by decide +kernel

private def d332 : MobiusHarmonicTree := .branch 47796900 d333 d334
private abbrev d336 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 38
private theorem p336 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223616 d336 = true := by decide +kernel

private abbrev d337 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 39
private theorem p337 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223680 d337 = true := by decide +kernel

private def d335 : MobiusHarmonicTree := .branch 50053881 d336 d337
private def d331 : MobiusHarmonicTree := .branch 97850781 d332 d335
private def d323 : MobiusHarmonicTree := .branch 197420384 d324 d331
private abbrev d341 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 40
private theorem p341 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223744 d341 = true := by decide +kernel

private abbrev d342 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 41
private theorem p342 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223808 d342 = true := by decide +kernel

private def d340 : MobiusHarmonicTree := .branch 47522896 d341 d342
private abbrev d344 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 42
private theorem p344 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223872 d344 = true := by decide +kernel

private abbrev d345 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 43
private theorem p345 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 223936 d345 = true := by decide +kernel

private def d343 : MobiusHarmonicTree := .branch 47973783 d344 d345
private def d339 : MobiusHarmonicTree := .branch 95496679 d340 d343
private abbrev d348 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 44
private theorem p348 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224000 d348 = true := by decide +kernel

private abbrev d349 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 45
private theorem p349 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224064 d349 = true := by decide +kernel

private def d347 : MobiusHarmonicTree := .branch 46317376 d348 d349
private abbrev d351 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 46
private theorem p351 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224128 d351 = true := by decide +kernel

private abbrev d352 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 47
private theorem p352 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224192 d352 = true := by decide +kernel

private def d350 : MobiusHarmonicTree := .branch 44488654 d351 d352
private def d346 : MobiusHarmonicTree := .branch 90806030 d347 d350
private def d338 : MobiusHarmonicTree := .branch 186302709 d339 d346
private def d322 : MobiusHarmonicTree := .branch 383723093 d323 d338
private abbrev d357 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 48
private theorem p357 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224256 d357 = true := by decide +kernel

private abbrev d358 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 49
private theorem p358 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224320 d358 = true := by decide +kernel

private def d356 : MobiusHarmonicTree := .branch 43683441 d357 d358
private abbrev d360 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 50
private theorem p360 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224384 d360 = true := by decide +kernel

private abbrev d361 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 51
private theorem p361 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224448 d361 = true := by decide +kernel

private def d359 : MobiusHarmonicTree := .branch 41559886 d360 d361
private def d355 : MobiusHarmonicTree := .branch 85243327 d356 d359
private abbrev d364 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 52
private theorem p364 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224512 d364 = true := by decide +kernel

private abbrev d365 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 53
private theorem p365 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224576 d365 = true := by decide +kernel

private def d363 : MobiusHarmonicTree := .branch 39987023 d364 d365
private abbrev d367 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 54
private theorem p367 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224640 d367 = true := by decide +kernel

private abbrev d368 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 55
private theorem p368 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224704 d368 = true := by decide +kernel

private def d366 : MobiusHarmonicTree := .branch 34534556 d367 d368
private def d362 : MobiusHarmonicTree := .branch 74521579 d363 d366
private def d354 : MobiusHarmonicTree := .branch 159764906 d355 d362
private abbrev d372 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 56
private theorem p372 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224768 d372 = true := by decide +kernel

private abbrev d373 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 57
private theorem p373 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224832 d373 = true := by decide +kernel

private def d371 : MobiusHarmonicTree := .branch 34337071 d372 d373
private abbrev d375 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 58
private theorem p375 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224896 d375 = true := by decide +kernel

private abbrev d376 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 59
private theorem p376 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 224960 d376 = true := by decide +kernel

private def d374 : MobiusHarmonicTree := .branch 37046698 d375 d376
private def d370 : MobiusHarmonicTree := .branch 71383769 d371 d374
private abbrev d379 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 60
private theorem p379 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225024 d379 = true := by decide +kernel

private abbrev d380 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 61
private theorem p380 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225088 d380 = true := by decide +kernel

private def d378 : MobiusHarmonicTree := .branch 35204337 d379 d380
private abbrev d382 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 62
private theorem p382 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225152 d382 = true := by decide +kernel

private abbrev d383 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 63
private theorem p383 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225216 d383 = true := by decide +kernel

private def d381 : MobiusHarmonicTree := .branch 35974217 d382 d383
private def d377 : MobiusHarmonicTree := .branch 71178554 d378 d381
private def d369 : MobiusHarmonicTree := .branch 142562323 d370 d377
private def d353 : MobiusHarmonicTree := .branch 302327229 d354 d369
private def d321 : MobiusHarmonicTree := .branch 686050322 d322 d353
private def d257 : MobiusHarmonicTree := .branch 1338396259 d258 d321
private abbrev d390 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 64
private theorem p390 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225280 d390 = true := by decide +kernel

private abbrev d391 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 65
private theorem p391 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225344 d391 = true := by decide +kernel

private def d389 : MobiusHarmonicTree := .branch 39259878 d390 d391
private abbrev d393 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 66
private theorem p393 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225408 d393 = true := by decide +kernel

private abbrev d394 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 67
private theorem p394 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225472 d394 = true := by decide +kernel

private def d392 : MobiusHarmonicTree := .branch 48107888 d393 d394
private def d388 : MobiusHarmonicTree := .branch 87367766 d389 d392
private abbrev d397 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 68
private theorem p397 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225536 d397 = true := by decide +kernel

private abbrev d398 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 69
private theorem p398 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225600 d398 = true := by decide +kernel

private def d396 : MobiusHarmonicTree := .branch 48829803 d397 d398
private abbrev d400 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 70
private theorem p400 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225664 d400 = true := by decide +kernel

private abbrev d401 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 71
private theorem p401 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225728 d401 = true := by decide +kernel

private def d399 : MobiusHarmonicTree := .branch 48124495 d400 d401
private def d395 : MobiusHarmonicTree := .branch 96954298 d396 d399
private def d387 : MobiusHarmonicTree := .branch 184322064 d388 d395
private abbrev d405 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 72
private theorem p405 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225792 d405 = true := by decide +kernel

private abbrev d406 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 73
private theorem p406 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225856 d406 = true := by decide +kernel

private def d404 : MobiusHarmonicTree := .branch 47109946 d405 d406
private abbrev d408 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 74
private theorem p408 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225920 d408 = true := by decide +kernel

private abbrev d409 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 75
private theorem p409 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 225984 d409 = true := by decide +kernel

private def d407 : MobiusHarmonicTree := .branch 48415042 d408 d409
private def d403 : MobiusHarmonicTree := .branch 95524988 d404 d407
private abbrev d412 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 76
private theorem p412 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226048 d412 = true := by decide +kernel

private abbrev d413 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 77
private theorem p413 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226112 d413 = true := by decide +kernel

private def d411 : MobiusHarmonicTree := .branch 42302331 d412 d413
private abbrev d415 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 78
private theorem p415 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226176 d415 = true := by decide +kernel

private abbrev d416 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 79
private theorem p416 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226240 d416 = true := by decide +kernel

private def d414 : MobiusHarmonicTree := .branch 41054139 d415 d416
private def d410 : MobiusHarmonicTree := .branch 83356470 d411 d414
private def d402 : MobiusHarmonicTree := .branch 178881458 d403 d410
private def d386 : MobiusHarmonicTree := .branch 363203522 d387 d402
private abbrev d421 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 80
private theorem p421 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226304 d421 = true := by decide +kernel

private abbrev d422 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 81
private theorem p422 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226368 d422 = true := by decide +kernel

private def d420 : MobiusHarmonicTree := .branch 35186169 d421 d422
private abbrev d424 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 82
private theorem p424 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226432 d424 = true := by decide +kernel

private abbrev d425 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 83
private theorem p425 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226496 d425 = true := by decide +kernel

private def d423 : MobiusHarmonicTree := .branch 34746807 d424 d425
private def d419 : MobiusHarmonicTree := .branch 69932976 d420 d423
private abbrev d428 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 84
private theorem p428 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226560 d428 = true := by decide +kernel

private abbrev d429 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 85
private theorem p429 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226624 d429 = true := by decide +kernel

private def d427 : MobiusHarmonicTree := .branch 31541552 d428 d429
private abbrev d431 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 86
private theorem p431 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226688 d431 = true := by decide +kernel

private abbrev d432 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 87
private theorem p432 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226752 d432 = true := by decide +kernel

private def d430 : MobiusHarmonicTree := .branch 29318455 d431 d432
private def d426 : MobiusHarmonicTree := .branch 60860007 d427 d430
private def d418 : MobiusHarmonicTree := .branch 130792983 d419 d426
private abbrev d436 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 88
private theorem p436 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226816 d436 = true := by decide +kernel

private abbrev d437 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 89
private theorem p437 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226880 d437 = true := by decide +kernel

private def d435 : MobiusHarmonicTree := .branch 32898529 d436 d437
private abbrev d439 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 90
private theorem p439 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 226944 d439 = true := by decide +kernel

private abbrev d440 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 91
private theorem p440 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227008 d440 = true := by decide +kernel

private def d438 : MobiusHarmonicTree := .branch 31294457 d439 d440
private def d434 : MobiusHarmonicTree := .branch 64192986 d435 d438
private abbrev d443 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 92
private theorem p443 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227072 d443 = true := by decide +kernel

private abbrev d444 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 93
private theorem p444 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227136 d444 = true := by decide +kernel

private def d442 : MobiusHarmonicTree := .branch 29308196 d443 d444
private abbrev d446 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 94
private theorem p446 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227200 d446 = true := by decide +kernel

private abbrev d447 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 95
private theorem p447 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227264 d447 = true := by decide +kernel

private def d445 : MobiusHarmonicTree := .branch 33648005 d446 d447
private def d441 : MobiusHarmonicTree := .branch 62956201 d442 d445
private def d433 : MobiusHarmonicTree := .branch 127149187 d434 d441
private def d417 : MobiusHarmonicTree := .branch 257942170 d418 d433
private def d385 : MobiusHarmonicTree := .branch 621145692 d386 d417
private abbrev d453 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 96
private theorem p453 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227328 d453 = true := by decide +kernel

private abbrev d454 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 97
private theorem p454 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227392 d454 = true := by decide +kernel

private def d452 : MobiusHarmonicTree := .branch 32147301 d453 d454
private abbrev d456 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 98
private theorem p456 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227456 d456 = true := by decide +kernel

private abbrev d457 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 99
private theorem p457 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227520 d457 = true := by decide +kernel

private def d455 : MobiusHarmonicTree := .branch 29439169 d456 d457
private def d451 : MobiusHarmonicTree := .branch 61586470 d452 d455
private abbrev d460 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 100
private theorem p460 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227584 d460 = true := by decide +kernel

private abbrev d461 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 101
private theorem p461 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227648 d461 = true := by decide +kernel

private def d459 : MobiusHarmonicTree := .branch 34966221 d460 d461
private abbrev d463 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 102
private theorem p463 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227712 d463 = true := by decide +kernel

private abbrev d464 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 103
private theorem p464 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227776 d464 = true := by decide +kernel

private def d462 : MobiusHarmonicTree := .branch 34793360 d463 d464
private def d458 : MobiusHarmonicTree := .branch 69759581 d459 d462
private def d450 : MobiusHarmonicTree := .branch 131346051 d451 d458
private abbrev d468 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 104
private theorem p468 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227840 d468 = true := by decide +kernel

private abbrev d469 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 105
private theorem p469 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227904 d469 = true := by decide +kernel

private def d467 : MobiusHarmonicTree := .branch 32290328 d468 d469
private abbrev d471 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 106
private theorem p471 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 227968 d471 = true := by decide +kernel

private abbrev d472 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 107
private theorem p472 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228032 d472 = true := by decide +kernel

private def d470 : MobiusHarmonicTree := .branch 28123362 d471 d472
private def d466 : MobiusHarmonicTree := .branch 60413690 d467 d470
private abbrev d475 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 108
private theorem p475 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228096 d475 = true := by decide +kernel

private abbrev d476 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 109
private theorem p476 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228160 d476 = true := by decide +kernel

private def d474 : MobiusHarmonicTree := .branch 25999634 d475 d476
private abbrev d478 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 110
private theorem p478 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228224 d478 = true := by decide +kernel

private abbrev d479 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 111
private theorem p479 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228288 d479 = true := by decide +kernel

private def d477 : MobiusHarmonicTree := .branch 28275781 d478 d479
private def d473 : MobiusHarmonicTree := .branch 54275415 d474 d477
private def d465 : MobiusHarmonicTree := .branch 114689105 d466 d473
private def d449 : MobiusHarmonicTree := .branch 246035156 d450 d465
private abbrev d484 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 112
private theorem p484 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228352 d484 = true := by decide +kernel

private abbrev d485 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 113
private theorem p485 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228416 d485 = true := by decide +kernel

private def d483 : MobiusHarmonicTree := .branch 24972055 d484 d485
private abbrev d487 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 114
private theorem p487 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228480 d487 = true := by decide +kernel

private abbrev d488 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 115
private theorem p488 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228544 d488 = true := by decide +kernel

private def d486 : MobiusHarmonicTree := .branch 28878193 d487 d488
private def d482 : MobiusHarmonicTree := .branch 53850248 d483 d486
private abbrev d491 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 116
private theorem p491 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228608 d491 = true := by decide +kernel

private abbrev d492 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 117
private theorem p492 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228672 d492 = true := by decide +kernel

private def d490 : MobiusHarmonicTree := .branch 35973160 d491 d492
private abbrev d494 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 118
private theorem p494 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228736 d494 = true := by decide +kernel

private abbrev d495 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 119
private theorem p495 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228800 d495 = true := by decide +kernel

private def d493 : MobiusHarmonicTree := .branch 36232589 d494 d495
private def d489 : MobiusHarmonicTree := .branch 72205749 d490 d493
private def d481 : MobiusHarmonicTree := .branch 126055997 d482 d489
private abbrev d499 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 120
private theorem p499 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228864 d499 = true := by decide +kernel

private abbrev d500 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 121
private theorem p500 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228928 d500 = true := by decide +kernel

private def d498 : MobiusHarmonicTree := .branch 38055582 d499 d500
private abbrev d502 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 122
private theorem p502 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 228992 d502 = true := by decide +kernel

private abbrev d503 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 123
private theorem p503 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229056 d503 = true := by decide +kernel

private def d501 : MobiusHarmonicTree := .branch 45272590 d502 d503
private def d497 : MobiusHarmonicTree := .branch 83328172 d498 d501
private abbrev d506 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 124
private theorem p506 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229120 d506 = true := by decide +kernel

private abbrev d507 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 125
private theorem p507 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229184 d507 = true := by decide +kernel

private def d505 : MobiusHarmonicTree := .branch 50413375 d506 d507
private abbrev d509 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 126
private theorem p509 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229248 d509 = true := by decide +kernel

private abbrev d510 : MobiusHarmonicTree := publishedLeaf 7 mobiusHarmonicBlock027 127
private theorem p510 : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 1 229312 d510 = true := by decide +kernel

private def d508 : MobiusHarmonicTree := .branch 52967650 d509 d510
private def d504 : MobiusHarmonicTree := .branch 103381025 d505 d508
private def d496 : MobiusHarmonicTree := .branch 186709197 d497 d504
private def d480 : MobiusHarmonicTree := .branch 312765194 d481 d496
private def d448 : MobiusHarmonicTree := .branch 558800350 d449 d480
private def d384 : MobiusHarmonicTree := .branch 1179946042 d385 d448
private def d256 : MobiusHarmonicTree := .branch 2518342301 d257 d384
private def d0 : MobiusHarmonicTree := .branch 3281953048 d1 d256

private theorem combined : mobiusHarmonicTreeCheck cg cm 1000000000 1078853 9 212992 d0 = true :=
  (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 8 212992 3281953048 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 212992 763610747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 212992 344235789 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 212992 127286702 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 212992 100704012 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 212992 77494083 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 212992 36456521 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 212992 15873730 _ _ (by decide) p8 p9 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 213120 20582791 _ _ (by decide) p11 p12 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 213248 41037562 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 213248 22544521 _ _ (by decide) p15 p16 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 213376 18493041 _ _ (by decide) p18 p19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 213504 23209929 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 213504 15859455 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 213504 7983726 _ _ (by decide) p23 p24 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 213632 7875729 _ _ (by decide) p26 p27 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 213760 7350474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 213760 4906147 _ _ (by decide) p30 p31 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 213888 2444327 _ _ (by decide) p33 p34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 214016 26582690 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 214016 11735697 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 214016 7286790 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 214016 6296977 _ _ (by decide) p39 p40 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 214144 989813 _ _ (by decide) p42 p43 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 214272 4448907 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 214272 1217757 _ _ (by decide) p46 p47 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 214400 3231150 _ _ (by decide) p49 p50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 214528 14846993 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 214528 7221044 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 214528 3429826 _ _ (by decide) p54 p55 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 214656 3791218 _ _ (by decide) p57 p58 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 214784 7625949 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 214784 2866989 _ _ (by decide) p61 p62 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 214912 4758960 _ _ (by decide) p64 p65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 215040 216949087 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 215040 95052340 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 215040 57670646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 215040 20715410 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 215040 5327678 _ _ (by decide) p71 p72 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 215168 15387732 _ _ (by decide) p74 p75 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 215296 36955236 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 215296 18680353 _ _ (by decide) p78 p79 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 215424 18274883 _ _ (by decide) p81 p82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 215552 37381694 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 215552 19522192 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 215552 12643544 _ _ (by decide) p86 p87 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 215680 6878648 _ _ (by decide) p89 p90 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 215808 17859502 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 215808 5123538 _ _ (by decide) p93 p94 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 215936 12735964 _ _ (by decide) p96 p97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 216064 121896747 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 216064 74354966 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 216064 38165061 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 216064 18845109 _ _ (by decide) p102 p103 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 216192 19319952 _ _ (by decide) p105 p106 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 216320 36189905 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 216320 19363575 _ _ (by decide) p109 p110 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 216448 16826330 _ _ (by decide) p112 p113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 216576 47541781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 216576 22251206 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 216576 10898215 _ _ (by decide) p117 p118 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 216704 11352991 _ _ (by decide) p120 p121 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 216832 25290575 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 216832 12227251 _ _ (by decide) p124 p125 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 216960 13063324 _ _ (by decide) p127 p128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 217088 419374958 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 217088 135536717 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 217088 99996712 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 217088 56459259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 217088 17511916 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 217088 7349880 _ _ (by decide) p135 p136 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 217216 10162036 _ _ (by decide) p138 p139 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 217344 38947343 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 217344 19028759 _ _ (by decide) p142 p143 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 217472 19918584 _ _ (by decide) p145 p146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 217600 43537453 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 217600 31631269 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 217600 15395505 _ _ (by decide) p150 p151 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 217728 16235764 _ _ (by decide) p153 p154 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 217856 11906184 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 217856 8168752 _ _ (by decide) p157 p158 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 217984 3737432 _ _ (by decide) p160 p161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 218112 35540005 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 218112 20919646 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 218112 13349945 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 218112 9721512 _ _ (by decide) p166 p167 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 218240 3628433 _ _ (by decide) p169 p170 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 218368 7569701 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 218368 3025915 _ _ (by decide) p173 p174 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 218496 4543786 _ _ (by decide) p176 p177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 218624 14620359 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 218624 6760778 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 218624 3264843 _ _ (by decide) p181 p182 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 218752 3495935 _ _ (by decide) p184 p185 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 218880 7859581 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 218880 6147869 _ _ (by decide) p188 p189 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 219008 1711712 _ _ (by decide) p191 p192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 219136 283838241 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 219136 83681767 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 219136 21434894 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 219136 3816754 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 219136 1031070 _ _ (by decide) p198 p199 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 219264 2785684 _ _ (by decide) p201 p202 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 219392 17618140 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 219392 5463618 _ _ (by decide) p205 p206 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 219520 12154522 _ _ (by decide) p208 p209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 219648 62246873 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 219648 28356129 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 219648 13836585 _ _ (by decide) p213 p214 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 219776 14519544 _ _ (by decide) p216 p217 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 219904 33890744 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 219904 16297530 _ _ (by decide) p220 p221 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 220032 17593214 _ _ (by decide) p223 p224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 220160 200156474 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 220160 88026651 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 220160 39296720 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 220160 16991501 _ _ (by decide) p229 p230 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 220288 22305219 _ _ (by decide) p232 p233 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 220416 48729931 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 220416 24655425 _ _ (by decide) p236 p237 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 220544 24074506 _ _ (by decide) p239 p240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 220672 112129823 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 220672 54672644 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 220672 25315445 _ _ (by decide) p244 p245 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 220800 29357199 _ _ (by decide) p247 p248 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 220928 57457179 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 220928 29340936 _ _ (by decide) p251 p252 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 221056 28116243 _ _ (by decide) p254 p255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 7 221184 2518342301 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 221184 1338396259 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 221184 652345937 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 221184 293015749 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 221184 128623097 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 221184 55040090 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 221184 27412786 _ _ (by decide) p263 p264 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 221312 27627304 _ _ (by decide) p266 p267 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 221440 73583007 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 221440 34021795 _ _ (by decide) p270 p271 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 221568 39561212 _ _ (by decide) p273 p274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 221696 164392652 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 221696 82356571 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 221696 45305802 _ _ (by decide) p278 p279 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 221824 37050769 _ _ (by decide) p281 p282 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 221952 82036081 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 221952 38568950 _ _ (by decide) p285 p286 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 222080 43467131 _ _ (by decide) p288 p289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 222208 359330188 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 222208 181835000 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 222208 93249296 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 222208 43284911 _ _ (by decide) p294 p295 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 222336 49964385 _ _ (by decide) p297 p298 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 222464 88585704 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 222464 46619335 _ _ (by decide) p301 p302 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 222592 41966369 _ _ (by decide) p304 p305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 222720 177495188 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 222720 86659163 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 222720 41713013 _ _ (by decide) p309 p310 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 222848 44946150 _ _ (by decide) p312 p313 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 222976 90836025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 222976 44131044 _ _ (by decide) p316 p317 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 223104 46704981 _ _ (by decide) p319 p320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 223232 686050322 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 223232 383723093 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 223232 197420384 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 223232 99569603 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 223232 48612526 _ _ (by decide) p326 p327 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 223360 50957077 _ _ (by decide) p329 p330 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 223488 97850781 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 223488 47796900 _ _ (by decide) p333 p334 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 223616 50053881 _ _ (by decide) p336 p337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 223744 186302709 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 223744 95496679 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 223744 47522896 _ _ (by decide) p341 p342 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 223872 47973783 _ _ (by decide) p344 p345 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 224000 90806030 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 224000 46317376 _ _ (by decide) p348 p349 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 224128 44488654 _ _ (by decide) p351 p352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 224256 302327229 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 224256 159764906 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 224256 85243327 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 224256 43683441 _ _ (by decide) p357 p358 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 224384 41559886 _ _ (by decide) p360 p361 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 224512 74521579 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 224512 39987023 _ _ (by decide) p364 p365 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 224640 34534556 _ _ (by decide) p367 p368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 224768 142562323 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 224768 71383769 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 224768 34337071 _ _ (by decide) p372 p373 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 224896 37046698 _ _ (by decide) p375 p376 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 225024 71178554 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 225024 35204337 _ _ (by decide) p379 p380 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 225152 35974217 _ _ (by decide) p382 p383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 6 225280 1179946042 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 225280 621145692 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 225280 363203522 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 225280 184322064 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 225280 87367766 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 225280 39259878 _ _ (by decide) p390 p391 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 225408 48107888 _ _ (by decide) p393 p394 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 225536 96954298 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 225536 48829803 _ _ (by decide) p397 p398 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 225664 48124495 _ _ (by decide) p400 p401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 225792 178881458 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 225792 95524988 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 225792 47109946 _ _ (by decide) p405 p406 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 225920 48415042 _ _ (by decide) p408 p409 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 226048 83356470 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 226048 42302331 _ _ (by decide) p412 p413 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 226176 41054139 _ _ (by decide) p415 p416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 226304 257942170 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 226304 130792983 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 226304 69932976 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 226304 35186169 _ _ (by decide) p421 p422 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 226432 34746807 _ _ (by decide) p424 p425 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 226560 60860007 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 226560 31541552 _ _ (by decide) p428 p429 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 226688 29318455 _ _ (by decide) p431 p432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 226816 127149187 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 226816 64192986 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 226816 32898529 _ _ (by decide) p436 p437 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 226944 31294457 _ _ (by decide) p439 p440 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 227072 62956201 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 227072 29308196 _ _ (by decide) p443 p444 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 227200 33648005 _ _ (by decide) p446 p447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 5 227328 558800350 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 227328 246035156 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 227328 131346051 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 227328 61586470 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 227328 32147301 _ _ (by decide) p453 p454 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 227456 29439169 _ _ (by decide) p456 p457 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 227584 69759581 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 227584 34966221 _ _ (by decide) p460 p461 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 227712 34793360 _ _ (by decide) p463 p464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 227840 114689105 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 227840 60413690 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 227840 32290328 _ _ (by decide) p468 p469 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 227968 28123362 _ _ (by decide) p471 p472 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 228096 54275415 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 228096 25999634 _ _ (by decide) p475 p476 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 228224 28275781 _ _ (by decide) p478 p479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 4 228352 312765194 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 228352 126055997 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 228352 53850248 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 228352 24972055 _ _ (by decide) p484 p485 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 228480 28878193 _ _ (by decide) p487 p488 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 228608 72205749 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 228608 35973160 _ _ (by decide) p491 p492 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 228736 36232589 _ _ (by decide) p494 p495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 3 228864 186709197 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 228864 83328172 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 228864 38055582 _ _ (by decide) p499 p500 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 228992 45272590 _ _ (by decide) p502 p503 (by decide +kernel)) (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 2 229120 103381025 _ _ (by decide) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 229120 50413375 _ _ (by decide) p506 p507 (by decide +kernel)) (mobiusHarmonicTreeCheck_join cg cm 1000000000 1078853 1 229248 52967650 _ _ (by decide) p509 p510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott

open Helfgott
theorem solution : mobiusHarmonicTreeCheck (mobiusTreeValue 16 mobiusTable1200001) (mobiusPrefixValue 16 mobiusHarmonic1078853) 1000000000 1078853 9 212992 (MobiusHarmonicTree.branch 3281953048 mobiusHarmonicBlock026 mobiusHarmonicBlock027) = true := Helfgott.combined

#print axioms solution
