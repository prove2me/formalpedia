-- Prove2me | solution 1 for Helfgott.mobiusReciprocalSqrtPair001_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T04:29:37.370699+00:00
-- url     : https://prove2.me/submissions/3c8d0fdf-f7b5-4874-ab28-597d52651dd3

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part00
import Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
import Mathlib.Tactic

section
set_option autoImplicit false
namespace Helfgott

theorem mobiusReciprocalSqrtTreeCheck_join (g : ℕ → ℤ) (Q B d offset : ℕ)
    (l r : MobiusReciprocalTree) (hoff : offset < B)
    (hl : mobiusReciprocalSqrtTreeCheck g Q B d offset l = true)
    (hr : mobiusReciprocalSqrtTreeCheck g Q B d (offset + 32 * 2 ^ d) r = true)
    (hjoin : mobiusReciprocalFinish l = mobiusReciprocalStart r) :
    mobiusReciprocalSqrtTreeCheck g Q B (d + 1) offset (.branch l r) = true := by
  have hnot : ¬ B ≤ offset := by omega
  simp only [mobiusReciprocalSqrtTreeCheck, if_neg hnot, hl, hr, hjoin,
    beq_self_eq_true, Bool.and_self]

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Helfgott

private def publishedReciprocalLeaf : ℕ → MobiusReciprocalTree → ℕ → MobiusReciprocalTree
  | 0, tree, _ => tree
  | d + 1, .branch l r, k =>
      if k < 2 ^ d then publishedReciprocalLeaf d l k else publishedReciprocalLeaf d r (k - 2 ^ d)
  | _, tree, _ => tree

private abbrev r8 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 0
private theorem rc8 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16384 r8 = true := by decide +kernel

private abbrev r9 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 1
private theorem rc9 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16448 r9 = true := by decide +kernel

private def r7 : MobiusReciprocalTree := .branch r8 r9
private abbrev r11 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 2
private theorem rc11 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16512 r11 = true := by decide +kernel

private abbrev r12 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 3
private theorem rc12 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16576 r12 = true := by decide +kernel

private def r10 : MobiusReciprocalTree := .branch r11 r12
private def r6 : MobiusReciprocalTree := .branch r7 r10
private abbrev r15 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 4
private theorem rc15 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16640 r15 = true := by decide +kernel

private abbrev r16 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 5
private theorem rc16 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16704 r16 = true := by decide +kernel

private def r14 : MobiusReciprocalTree := .branch r15 r16
private abbrev r18 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 6
private theorem rc18 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16768 r18 = true := by decide +kernel

private abbrev r19 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 7
private theorem rc19 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16832 r19 = true := by decide +kernel

private def r17 : MobiusReciprocalTree := .branch r18 r19
private def r13 : MobiusReciprocalTree := .branch r14 r17
private def r5 : MobiusReciprocalTree := .branch r6 r13
private abbrev r23 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 8
private theorem rc23 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16896 r23 = true := by decide +kernel

private abbrev r24 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 9
private theorem rc24 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16960 r24 = true := by decide +kernel

private def r22 : MobiusReciprocalTree := .branch r23 r24
private abbrev r26 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 10
private theorem rc26 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17024 r26 = true := by decide +kernel

private abbrev r27 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 11
private theorem rc27 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17088 r27 = true := by decide +kernel

private def r25 : MobiusReciprocalTree := .branch r26 r27
private def r21 : MobiusReciprocalTree := .branch r22 r25
private abbrev r30 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 12
private theorem rc30 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17152 r30 = true := by decide +kernel

private abbrev r31 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 13
private theorem rc31 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17216 r31 = true := by decide +kernel

private def r29 : MobiusReciprocalTree := .branch r30 r31
private abbrev r33 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 14
private theorem rc33 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17280 r33 = true := by decide +kernel

private abbrev r34 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 15
private theorem rc34 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17344 r34 = true := by decide +kernel

private def r32 : MobiusReciprocalTree := .branch r33 r34
private def r28 : MobiusReciprocalTree := .branch r29 r32
private def r20 : MobiusReciprocalTree := .branch r21 r28
private def r4 : MobiusReciprocalTree := .branch r5 r20
private abbrev r39 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 16
private theorem rc39 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17408 r39 = true := by decide +kernel

private abbrev r40 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 17
private theorem rc40 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17472 r40 = true := by decide +kernel

private def r38 : MobiusReciprocalTree := .branch r39 r40
private abbrev r42 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 18
private theorem rc42 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17536 r42 = true := by decide +kernel

private abbrev r43 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 19
private theorem rc43 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17600 r43 = true := by decide +kernel

private def r41 : MobiusReciprocalTree := .branch r42 r43
private def r37 : MobiusReciprocalTree := .branch r38 r41
private abbrev r46 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 20
private theorem rc46 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17664 r46 = true := by decide +kernel

private abbrev r47 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 21
private theorem rc47 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17728 r47 = true := by decide +kernel

private def r45 : MobiusReciprocalTree := .branch r46 r47
private abbrev r49 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 22
private theorem rc49 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17792 r49 = true := by decide +kernel

private abbrev r50 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 23
private theorem rc50 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17856 r50 = true := by decide +kernel

private def r48 : MobiusReciprocalTree := .branch r49 r50
private def r44 : MobiusReciprocalTree := .branch r45 r48
private def r36 : MobiusReciprocalTree := .branch r37 r44
private abbrev r54 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 24
private theorem rc54 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17920 r54 = true := by decide +kernel

private abbrev r55 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 25
private theorem rc55 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17984 r55 = true := by decide +kernel

private def r53 : MobiusReciprocalTree := .branch r54 r55
private abbrev r57 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 26
private theorem rc57 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18048 r57 = true := by decide +kernel

private abbrev r58 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 27
private theorem rc58 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18112 r58 = true := by decide +kernel

private def r56 : MobiusReciprocalTree := .branch r57 r58
private def r52 : MobiusReciprocalTree := .branch r53 r56
private abbrev r61 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 28
private theorem rc61 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18176 r61 = true := by decide +kernel

private abbrev r62 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 29
private theorem rc62 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18240 r62 = true := by decide +kernel

private def r60 : MobiusReciprocalTree := .branch r61 r62
private abbrev r64 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 30
private theorem rc64 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18304 r64 = true := by decide +kernel

private abbrev r65 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 31
private theorem rc65 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18368 r65 = true := by decide +kernel

private def r63 : MobiusReciprocalTree := .branch r64 r65
private def r59 : MobiusReciprocalTree := .branch r60 r63
private def r51 : MobiusReciprocalTree := .branch r52 r59
private def r35 : MobiusReciprocalTree := .branch r36 r51
private def r3 : MobiusReciprocalTree := .branch r4 r35
private abbrev r71 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 32
private theorem rc71 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18432 r71 = true := by decide +kernel

private abbrev r72 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 33
private theorem rc72 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18496 r72 = true := by decide +kernel

private def r70 : MobiusReciprocalTree := .branch r71 r72
private abbrev r74 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 34
private theorem rc74 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18560 r74 = true := by decide +kernel

private abbrev r75 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 35
private theorem rc75 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18624 r75 = true := by decide +kernel

private def r73 : MobiusReciprocalTree := .branch r74 r75
private def r69 : MobiusReciprocalTree := .branch r70 r73
private abbrev r78 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 36
private theorem rc78 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18688 r78 = true := by decide +kernel

private abbrev r79 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 37
private theorem rc79 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18752 r79 = true := by decide +kernel

private def r77 : MobiusReciprocalTree := .branch r78 r79
private abbrev r81 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 38
private theorem rc81 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18816 r81 = true := by decide +kernel

private abbrev r82 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 39
private theorem rc82 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18880 r82 = true := by decide +kernel

private def r80 : MobiusReciprocalTree := .branch r81 r82
private def r76 : MobiusReciprocalTree := .branch r77 r80
private def r68 : MobiusReciprocalTree := .branch r69 r76
private abbrev r86 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 40
private theorem rc86 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18944 r86 = true := by decide +kernel

private abbrev r87 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 41
private theorem rc87 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19008 r87 = true := by decide +kernel

private def r85 : MobiusReciprocalTree := .branch r86 r87
private abbrev r89 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 42
private theorem rc89 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19072 r89 = true := by decide +kernel

private abbrev r90 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 43
private theorem rc90 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19136 r90 = true := by decide +kernel

private def r88 : MobiusReciprocalTree := .branch r89 r90
private def r84 : MobiusReciprocalTree := .branch r85 r88
private abbrev r93 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 44
private theorem rc93 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19200 r93 = true := by decide +kernel

private abbrev r94 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 45
private theorem rc94 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19264 r94 = true := by decide +kernel

private def r92 : MobiusReciprocalTree := .branch r93 r94
private abbrev r96 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 46
private theorem rc96 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19328 r96 = true := by decide +kernel

private abbrev r97 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 47
private theorem rc97 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19392 r97 = true := by decide +kernel

private def r95 : MobiusReciprocalTree := .branch r96 r97
private def r91 : MobiusReciprocalTree := .branch r92 r95
private def r83 : MobiusReciprocalTree := .branch r84 r91
private def r67 : MobiusReciprocalTree := .branch r68 r83
private abbrev r102 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 48
private theorem rc102 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19456 r102 = true := by decide +kernel

private abbrev r103 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 49
private theorem rc103 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19520 r103 = true := by decide +kernel

private def r101 : MobiusReciprocalTree := .branch r102 r103
private abbrev r105 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 50
private theorem rc105 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19584 r105 = true := by decide +kernel

private abbrev r106 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 51
private theorem rc106 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19648 r106 = true := by decide +kernel

private def r104 : MobiusReciprocalTree := .branch r105 r106
private def r100 : MobiusReciprocalTree := .branch r101 r104
private abbrev r109 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 52
private theorem rc109 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19712 r109 = true := by decide +kernel

private abbrev r110 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 53
private theorem rc110 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19776 r110 = true := by decide +kernel

private def r108 : MobiusReciprocalTree := .branch r109 r110
private abbrev r112 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 54
private theorem rc112 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19840 r112 = true := by decide +kernel

private abbrev r113 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 55
private theorem rc113 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19904 r113 = true := by decide +kernel

private def r111 : MobiusReciprocalTree := .branch r112 r113
private def r107 : MobiusReciprocalTree := .branch r108 r111
private def r99 : MobiusReciprocalTree := .branch r100 r107
private abbrev r117 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 56
private theorem rc117 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19968 r117 = true := by decide +kernel

private abbrev r118 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 57
private theorem rc118 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20032 r118 = true := by decide +kernel

private def r116 : MobiusReciprocalTree := .branch r117 r118
private abbrev r120 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 58
private theorem rc120 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20096 r120 = true := by decide +kernel

private abbrev r121 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 59
private theorem rc121 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20160 r121 = true := by decide +kernel

private def r119 : MobiusReciprocalTree := .branch r120 r121
private def r115 : MobiusReciprocalTree := .branch r116 r119
private abbrev r124 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 60
private theorem rc124 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20224 r124 = true := by decide +kernel

private abbrev r125 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 61
private theorem rc125 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20288 r125 = true := by decide +kernel

private def r123 : MobiusReciprocalTree := .branch r124 r125
private abbrev r127 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 62
private theorem rc127 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20352 r127 = true := by decide +kernel

private abbrev r128 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 63
private theorem rc128 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20416 r128 = true := by decide +kernel

private def r126 : MobiusReciprocalTree := .branch r127 r128
private def r122 : MobiusReciprocalTree := .branch r123 r126
private def r114 : MobiusReciprocalTree := .branch r115 r122
private def r98 : MobiusReciprocalTree := .branch r99 r114
private def r66 : MobiusReciprocalTree := .branch r67 r98
private def r2 : MobiusReciprocalTree := .branch r3 r66
private abbrev r135 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 64
private theorem rc135 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20480 r135 = true := by decide +kernel

private abbrev r136 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 65
private theorem rc136 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20544 r136 = true := by decide +kernel

private def r134 : MobiusReciprocalTree := .branch r135 r136
private abbrev r138 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 66
private theorem rc138 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20608 r138 = true := by decide +kernel

private abbrev r139 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 67
private theorem rc139 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20672 r139 = true := by decide +kernel

private def r137 : MobiusReciprocalTree := .branch r138 r139
private def r133 : MobiusReciprocalTree := .branch r134 r137
private abbrev r142 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 68
private theorem rc142 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20736 r142 = true := by decide +kernel

private abbrev r143 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 69
private theorem rc143 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20800 r143 = true := by decide +kernel

private def r141 : MobiusReciprocalTree := .branch r142 r143
private abbrev r145 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 70
private theorem rc145 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20864 r145 = true := by decide +kernel

private abbrev r146 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 71
private theorem rc146 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20928 r146 = true := by decide +kernel

private def r144 : MobiusReciprocalTree := .branch r145 r146
private def r140 : MobiusReciprocalTree := .branch r141 r144
private def r132 : MobiusReciprocalTree := .branch r133 r140
private abbrev r150 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 72
private theorem rc150 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20992 r150 = true := by decide +kernel

private abbrev r151 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 73
private theorem rc151 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21056 r151 = true := by decide +kernel

private def r149 : MobiusReciprocalTree := .branch r150 r151
private abbrev r153 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 74
private theorem rc153 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21120 r153 = true := by decide +kernel

private abbrev r154 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 75
private theorem rc154 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21184 r154 = true := by decide +kernel

private def r152 : MobiusReciprocalTree := .branch r153 r154
private def r148 : MobiusReciprocalTree := .branch r149 r152
private abbrev r157 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 76
private theorem rc157 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21248 r157 = true := by decide +kernel

private abbrev r158 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 77
private theorem rc158 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21312 r158 = true := by decide +kernel

private def r156 : MobiusReciprocalTree := .branch r157 r158
private abbrev r160 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 78
private theorem rc160 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21376 r160 = true := by decide +kernel

private abbrev r161 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 79
private theorem rc161 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21440 r161 = true := by decide +kernel

private def r159 : MobiusReciprocalTree := .branch r160 r161
private def r155 : MobiusReciprocalTree := .branch r156 r159
private def r147 : MobiusReciprocalTree := .branch r148 r155
private def r131 : MobiusReciprocalTree := .branch r132 r147
private abbrev r166 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 80
private theorem rc166 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21504 r166 = true := by decide +kernel

private abbrev r167 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 81
private theorem rc167 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21568 r167 = true := by decide +kernel

private def r165 : MobiusReciprocalTree := .branch r166 r167
private abbrev r169 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 82
private theorem rc169 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21632 r169 = true := by decide +kernel

private abbrev r170 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 83
private theorem rc170 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21696 r170 = true := by decide +kernel

private def r168 : MobiusReciprocalTree := .branch r169 r170
private def r164 : MobiusReciprocalTree := .branch r165 r168
private abbrev r173 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 84
private theorem rc173 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21760 r173 = true := by decide +kernel

private abbrev r174 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 85
private theorem rc174 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21824 r174 = true := by decide +kernel

private def r172 : MobiusReciprocalTree := .branch r173 r174
private abbrev r176 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 86
private theorem rc176 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21888 r176 = true := by decide +kernel

private abbrev r177 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 87
private theorem rc177 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21952 r177 = true := by decide +kernel

private def r175 : MobiusReciprocalTree := .branch r176 r177
private def r171 : MobiusReciprocalTree := .branch r172 r175
private def r163 : MobiusReciprocalTree := .branch r164 r171
private abbrev r181 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 88
private theorem rc181 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22016 r181 = true := by decide +kernel

private abbrev r182 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 89
private theorem rc182 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22080 r182 = true := by decide +kernel

private def r180 : MobiusReciprocalTree := .branch r181 r182
private abbrev r184 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 90
private theorem rc184 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22144 r184 = true := by decide +kernel

private abbrev r185 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 91
private theorem rc185 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22208 r185 = true := by decide +kernel

private def r183 : MobiusReciprocalTree := .branch r184 r185
private def r179 : MobiusReciprocalTree := .branch r180 r183
private abbrev r188 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 92
private theorem rc188 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22272 r188 = true := by decide +kernel

private abbrev r189 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 93
private theorem rc189 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22336 r189 = true := by decide +kernel

private def r187 : MobiusReciprocalTree := .branch r188 r189
private abbrev r191 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 94
private theorem rc191 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22400 r191 = true := by decide +kernel

private abbrev r192 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 95
private theorem rc192 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22464 r192 = true := by decide +kernel

private def r190 : MobiusReciprocalTree := .branch r191 r192
private def r186 : MobiusReciprocalTree := .branch r187 r190
private def r178 : MobiusReciprocalTree := .branch r179 r186
private def r162 : MobiusReciprocalTree := .branch r163 r178
private def r130 : MobiusReciprocalTree := .branch r131 r162
private abbrev r198 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 96
private theorem rc198 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22528 r198 = true := by decide +kernel

private abbrev r199 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 97
private theorem rc199 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22592 r199 = true := by decide +kernel

private def r197 : MobiusReciprocalTree := .branch r198 r199
private abbrev r201 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 98
private theorem rc201 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22656 r201 = true := by decide +kernel

private abbrev r202 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 99
private theorem rc202 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22720 r202 = true := by decide +kernel

private def r200 : MobiusReciprocalTree := .branch r201 r202
private def r196 : MobiusReciprocalTree := .branch r197 r200
private abbrev r205 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 100
private theorem rc205 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22784 r205 = true := by decide +kernel

private abbrev r206 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 101
private theorem rc206 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22848 r206 = true := by decide +kernel

private def r204 : MobiusReciprocalTree := .branch r205 r206
private abbrev r208 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 102
private theorem rc208 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22912 r208 = true := by decide +kernel

private abbrev r209 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 103
private theorem rc209 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22976 r209 = true := by decide +kernel

private def r207 : MobiusReciprocalTree := .branch r208 r209
private def r203 : MobiusReciprocalTree := .branch r204 r207
private def r195 : MobiusReciprocalTree := .branch r196 r203
private abbrev r213 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 104
private theorem rc213 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23040 r213 = true := by decide +kernel

private abbrev r214 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 105
private theorem rc214 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23104 r214 = true := by decide +kernel

private def r212 : MobiusReciprocalTree := .branch r213 r214
private abbrev r216 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 106
private theorem rc216 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23168 r216 = true := by decide +kernel

private abbrev r217 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 107
private theorem rc217 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23232 r217 = true := by decide +kernel

private def r215 : MobiusReciprocalTree := .branch r216 r217
private def r211 : MobiusReciprocalTree := .branch r212 r215
private abbrev r220 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 108
private theorem rc220 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23296 r220 = true := by decide +kernel

private abbrev r221 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 109
private theorem rc221 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23360 r221 = true := by decide +kernel

private def r219 : MobiusReciprocalTree := .branch r220 r221
private abbrev r223 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 110
private theorem rc223 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23424 r223 = true := by decide +kernel

private abbrev r224 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 111
private theorem rc224 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23488 r224 = true := by decide +kernel

private def r222 : MobiusReciprocalTree := .branch r223 r224
private def r218 : MobiusReciprocalTree := .branch r219 r222
private def r210 : MobiusReciprocalTree := .branch r211 r218
private def r194 : MobiusReciprocalTree := .branch r195 r210
private abbrev r229 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 112
private theorem rc229 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23552 r229 = true := by decide +kernel

private abbrev r230 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 113
private theorem rc230 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23616 r230 = true := by decide +kernel

private def r228 : MobiusReciprocalTree := .branch r229 r230
private abbrev r232 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 114
private theorem rc232 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23680 r232 = true := by decide +kernel

private abbrev r233 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 115
private theorem rc233 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23744 r233 = true := by decide +kernel

private def r231 : MobiusReciprocalTree := .branch r232 r233
private def r227 : MobiusReciprocalTree := .branch r228 r231
private abbrev r236 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 116
private theorem rc236 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23808 r236 = true := by decide +kernel

private abbrev r237 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 117
private theorem rc237 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23872 r237 = true := by decide +kernel

private def r235 : MobiusReciprocalTree := .branch r236 r237
private abbrev r239 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 118
private theorem rc239 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23936 r239 = true := by decide +kernel

private abbrev r240 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 119
private theorem rc240 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24000 r240 = true := by decide +kernel

private def r238 : MobiusReciprocalTree := .branch r239 r240
private def r234 : MobiusReciprocalTree := .branch r235 r238
private def r226 : MobiusReciprocalTree := .branch r227 r234
private abbrev r244 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 120
private theorem rc244 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24064 r244 = true := by decide +kernel

private abbrev r245 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 121
private theorem rc245 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24128 r245 = true := by decide +kernel

private def r243 : MobiusReciprocalTree := .branch r244 r245
private abbrev r247 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 122
private theorem rc247 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24192 r247 = true := by decide +kernel

private abbrev r248 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 123
private theorem rc248 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24256 r248 = true := by decide +kernel

private def r246 : MobiusReciprocalTree := .branch r247 r248
private def r242 : MobiusReciprocalTree := .branch r243 r246
private abbrev r251 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 124
private theorem rc251 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24320 r251 = true := by decide +kernel

private abbrev r252 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 125
private theorem rc252 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24384 r252 = true := by decide +kernel

private def r250 : MobiusReciprocalTree := .branch r251 r252
private abbrev r254 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 126
private theorem rc254 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24448 r254 = true := by decide +kernel

private abbrev r255 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block002 127
private theorem rc255 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24512 r255 = true := by decide +kernel

private def r253 : MobiusReciprocalTree := .branch r254 r255
private def r249 : MobiusReciprocalTree := .branch r250 r253
private def r241 : MobiusReciprocalTree := .branch r242 r249
private def r225 : MobiusReciprocalTree := .branch r226 r241
private def r193 : MobiusReciprocalTree := .branch r194 r225
private def r129 : MobiusReciprocalTree := .branch r130 r193
private def r1 : MobiusReciprocalTree := .branch r2 r129
private abbrev r263 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 0
private theorem rc263 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24576 r263 = true := by decide +kernel

private abbrev r264 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 1
private theorem rc264 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24640 r264 = true := by decide +kernel

private def r262 : MobiusReciprocalTree := .branch r263 r264
private abbrev r266 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 2
private theorem rc266 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24704 r266 = true := by decide +kernel

private abbrev r267 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 3
private theorem rc267 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24768 r267 = true := by decide +kernel

private def r265 : MobiusReciprocalTree := .branch r266 r267
private def r261 : MobiusReciprocalTree := .branch r262 r265
private abbrev r270 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 4
private theorem rc270 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24832 r270 = true := by decide +kernel

private abbrev r271 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 5
private theorem rc271 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24896 r271 = true := by decide +kernel

private def r269 : MobiusReciprocalTree := .branch r270 r271
private abbrev r273 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 6
private theorem rc273 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24960 r273 = true := by decide +kernel

private abbrev r274 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 7
private theorem rc274 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25024 r274 = true := by decide +kernel

private def r272 : MobiusReciprocalTree := .branch r273 r274
private def r268 : MobiusReciprocalTree := .branch r269 r272
private def r260 : MobiusReciprocalTree := .branch r261 r268
private abbrev r278 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 8
private theorem rc278 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25088 r278 = true := by decide +kernel

private abbrev r279 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 9
private theorem rc279 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25152 r279 = true := by decide +kernel

private def r277 : MobiusReciprocalTree := .branch r278 r279
private abbrev r281 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 10
private theorem rc281 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25216 r281 = true := by decide +kernel

private abbrev r282 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 11
private theorem rc282 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25280 r282 = true := by decide +kernel

private def r280 : MobiusReciprocalTree := .branch r281 r282
private def r276 : MobiusReciprocalTree := .branch r277 r280
private abbrev r285 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 12
private theorem rc285 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25344 r285 = true := by decide +kernel

private abbrev r286 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 13
private theorem rc286 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25408 r286 = true := by decide +kernel

private def r284 : MobiusReciprocalTree := .branch r285 r286
private abbrev r288 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 14
private theorem rc288 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25472 r288 = true := by decide +kernel

private abbrev r289 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 15
private theorem rc289 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25536 r289 = true := by decide +kernel

private def r287 : MobiusReciprocalTree := .branch r288 r289
private def r283 : MobiusReciprocalTree := .branch r284 r287
private def r275 : MobiusReciprocalTree := .branch r276 r283
private def r259 : MobiusReciprocalTree := .branch r260 r275
private abbrev r294 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 16
private theorem rc294 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25600 r294 = true := by decide +kernel

private abbrev r295 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 17
private theorem rc295 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25664 r295 = true := by decide +kernel

private def r293 : MobiusReciprocalTree := .branch r294 r295
private abbrev r297 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 18
private theorem rc297 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25728 r297 = true := by decide +kernel

private abbrev r298 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 19
private theorem rc298 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25792 r298 = true := by decide +kernel

private def r296 : MobiusReciprocalTree := .branch r297 r298
private def r292 : MobiusReciprocalTree := .branch r293 r296
private abbrev r301 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 20
private theorem rc301 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25856 r301 = true := by decide +kernel

private abbrev r302 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 21
private theorem rc302 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25920 r302 = true := by decide +kernel

private def r300 : MobiusReciprocalTree := .branch r301 r302
private abbrev r304 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 22
private theorem rc304 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25984 r304 = true := by decide +kernel

private abbrev r305 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 23
private theorem rc305 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26048 r305 = true := by decide +kernel

private def r303 : MobiusReciprocalTree := .branch r304 r305
private def r299 : MobiusReciprocalTree := .branch r300 r303
private def r291 : MobiusReciprocalTree := .branch r292 r299
private abbrev r309 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 24
private theorem rc309 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26112 r309 = true := by decide +kernel

private abbrev r310 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 25
private theorem rc310 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26176 r310 = true := by decide +kernel

private def r308 : MobiusReciprocalTree := .branch r309 r310
private abbrev r312 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 26
private theorem rc312 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26240 r312 = true := by decide +kernel

private abbrev r313 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 27
private theorem rc313 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26304 r313 = true := by decide +kernel

private def r311 : MobiusReciprocalTree := .branch r312 r313
private def r307 : MobiusReciprocalTree := .branch r308 r311
private abbrev r316 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 28
private theorem rc316 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26368 r316 = true := by decide +kernel

private abbrev r317 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 29
private theorem rc317 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26432 r317 = true := by decide +kernel

private def r315 : MobiusReciprocalTree := .branch r316 r317
private abbrev r319 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 30
private theorem rc319 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26496 r319 = true := by decide +kernel

private abbrev r320 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 31
private theorem rc320 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26560 r320 = true := by decide +kernel

private def r318 : MobiusReciprocalTree := .branch r319 r320
private def r314 : MobiusReciprocalTree := .branch r315 r318
private def r306 : MobiusReciprocalTree := .branch r307 r314
private def r290 : MobiusReciprocalTree := .branch r291 r306
private def r258 : MobiusReciprocalTree := .branch r259 r290
private abbrev r326 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 32
private theorem rc326 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26624 r326 = true := by decide +kernel

private abbrev r327 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 33
private theorem rc327 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26688 r327 = true := by decide +kernel

private def r325 : MobiusReciprocalTree := .branch r326 r327
private abbrev r329 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 34
private theorem rc329 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26752 r329 = true := by decide +kernel

private abbrev r330 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 35
private theorem rc330 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26816 r330 = true := by decide +kernel

private def r328 : MobiusReciprocalTree := .branch r329 r330
private def r324 : MobiusReciprocalTree := .branch r325 r328
private abbrev r333 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 36
private theorem rc333 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26880 r333 = true := by decide +kernel

private abbrev r334 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 37
private theorem rc334 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26944 r334 = true := by decide +kernel

private def r332 : MobiusReciprocalTree := .branch r333 r334
private abbrev r336 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 38
private theorem rc336 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27008 r336 = true := by decide +kernel

private abbrev r337 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 39
private theorem rc337 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27072 r337 = true := by decide +kernel

private def r335 : MobiusReciprocalTree := .branch r336 r337
private def r331 : MobiusReciprocalTree := .branch r332 r335
private def r323 : MobiusReciprocalTree := .branch r324 r331
private abbrev r341 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 40
private theorem rc341 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27136 r341 = true := by decide +kernel

private abbrev r342 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 41
private theorem rc342 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27200 r342 = true := by decide +kernel

private def r340 : MobiusReciprocalTree := .branch r341 r342
private abbrev r344 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 42
private theorem rc344 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27264 r344 = true := by decide +kernel

private abbrev r345 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 43
private theorem rc345 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27328 r345 = true := by decide +kernel

private def r343 : MobiusReciprocalTree := .branch r344 r345
private def r339 : MobiusReciprocalTree := .branch r340 r343
private abbrev r348 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 44
private theorem rc348 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27392 r348 = true := by decide +kernel

private abbrev r349 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 45
private theorem rc349 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27456 r349 = true := by decide +kernel

private def r347 : MobiusReciprocalTree := .branch r348 r349
private abbrev r351 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 46
private theorem rc351 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27520 r351 = true := by decide +kernel

private abbrev r352 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 47
private theorem rc352 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27584 r352 = true := by decide +kernel

private def r350 : MobiusReciprocalTree := .branch r351 r352
private def r346 : MobiusReciprocalTree := .branch r347 r350
private def r338 : MobiusReciprocalTree := .branch r339 r346
private def r322 : MobiusReciprocalTree := .branch r323 r338
private abbrev r357 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 48
private theorem rc357 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27648 r357 = true := by decide +kernel

private abbrev r358 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 49
private theorem rc358 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27712 r358 = true := by decide +kernel

private def r356 : MobiusReciprocalTree := .branch r357 r358
private abbrev r360 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 50
private theorem rc360 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27776 r360 = true := by decide +kernel

private abbrev r361 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 51
private theorem rc361 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27840 r361 = true := by decide +kernel

private def r359 : MobiusReciprocalTree := .branch r360 r361
private def r355 : MobiusReciprocalTree := .branch r356 r359
private abbrev r364 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 52
private theorem rc364 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27904 r364 = true := by decide +kernel

private abbrev r365 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 53
private theorem rc365 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27968 r365 = true := by decide +kernel

private def r363 : MobiusReciprocalTree := .branch r364 r365
private abbrev r367 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 54
private theorem rc367 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28032 r367 = true := by decide +kernel

private abbrev r368 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 55
private theorem rc368 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28096 r368 = true := by decide +kernel

private def r366 : MobiusReciprocalTree := .branch r367 r368
private def r362 : MobiusReciprocalTree := .branch r363 r366
private def r354 : MobiusReciprocalTree := .branch r355 r362
private abbrev r372 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 56
private theorem rc372 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28160 r372 = true := by decide +kernel

private abbrev r373 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 57
private theorem rc373 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28224 r373 = true := by decide +kernel

private def r371 : MobiusReciprocalTree := .branch r372 r373
private abbrev r375 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 58
private theorem rc375 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28288 r375 = true := by decide +kernel

private abbrev r376 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 59
private theorem rc376 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28352 r376 = true := by decide +kernel

private def r374 : MobiusReciprocalTree := .branch r375 r376
private def r370 : MobiusReciprocalTree := .branch r371 r374
private abbrev r379 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 60
private theorem rc379 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28416 r379 = true := by decide +kernel

private abbrev r380 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 61
private theorem rc380 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28480 r380 = true := by decide +kernel

private def r378 : MobiusReciprocalTree := .branch r379 r380
private abbrev r382 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 62
private theorem rc382 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28544 r382 = true := by decide +kernel

private abbrev r383 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 63
private theorem rc383 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28608 r383 = true := by decide +kernel

private def r381 : MobiusReciprocalTree := .branch r382 r383
private def r377 : MobiusReciprocalTree := .branch r378 r381
private def r369 : MobiusReciprocalTree := .branch r370 r377
private def r353 : MobiusReciprocalTree := .branch r354 r369
private def r321 : MobiusReciprocalTree := .branch r322 r353
private def r257 : MobiusReciprocalTree := .branch r258 r321
private abbrev r390 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 64
private theorem rc390 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28672 r390 = true := by decide +kernel

private abbrev r391 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 65
private theorem rc391 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28736 r391 = true := by decide +kernel

private def r389 : MobiusReciprocalTree := .branch r390 r391
private abbrev r393 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 66
private theorem rc393 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28800 r393 = true := by decide +kernel

private abbrev r394 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 67
private theorem rc394 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28864 r394 = true := by decide +kernel

private def r392 : MobiusReciprocalTree := .branch r393 r394
private def r388 : MobiusReciprocalTree := .branch r389 r392
private abbrev r397 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 68
private theorem rc397 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28928 r397 = true := by decide +kernel

private abbrev r398 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 69
private theorem rc398 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28992 r398 = true := by decide +kernel

private def r396 : MobiusReciprocalTree := .branch r397 r398
private abbrev r400 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 70
private theorem rc400 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29056 r400 = true := by decide +kernel

private abbrev r401 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 71
private theorem rc401 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29120 r401 = true := by decide +kernel

private def r399 : MobiusReciprocalTree := .branch r400 r401
private def r395 : MobiusReciprocalTree := .branch r396 r399
private def r387 : MobiusReciprocalTree := .branch r388 r395
private abbrev r405 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 72
private theorem rc405 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29184 r405 = true := by decide +kernel

private abbrev r406 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 73
private theorem rc406 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29248 r406 = true := by decide +kernel

private def r404 : MobiusReciprocalTree := .branch r405 r406
private abbrev r408 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 74
private theorem rc408 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29312 r408 = true := by decide +kernel

private abbrev r409 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 75
private theorem rc409 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29376 r409 = true := by decide +kernel

private def r407 : MobiusReciprocalTree := .branch r408 r409
private def r403 : MobiusReciprocalTree := .branch r404 r407
private abbrev r412 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 76
private theorem rc412 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29440 r412 = true := by decide +kernel

private abbrev r413 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 77
private theorem rc413 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29504 r413 = true := by decide +kernel

private def r411 : MobiusReciprocalTree := .branch r412 r413
private abbrev r415 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 78
private theorem rc415 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29568 r415 = true := by decide +kernel

private abbrev r416 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 79
private theorem rc416 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29632 r416 = true := by decide +kernel

private def r414 : MobiusReciprocalTree := .branch r415 r416
private def r410 : MobiusReciprocalTree := .branch r411 r414
private def r402 : MobiusReciprocalTree := .branch r403 r410
private def r386 : MobiusReciprocalTree := .branch r387 r402
private abbrev r421 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 80
private theorem rc421 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29696 r421 = true := by decide +kernel

private abbrev r422 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 81
private theorem rc422 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29760 r422 = true := by decide +kernel

private def r420 : MobiusReciprocalTree := .branch r421 r422
private abbrev r424 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 82
private theorem rc424 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29824 r424 = true := by decide +kernel

private abbrev r425 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 83
private theorem rc425 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29888 r425 = true := by decide +kernel

private def r423 : MobiusReciprocalTree := .branch r424 r425
private def r419 : MobiusReciprocalTree := .branch r420 r423
private abbrev r428 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 84
private theorem rc428 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29952 r428 = true := by decide +kernel

private abbrev r429 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 85
private theorem rc429 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30016 r429 = true := by decide +kernel

private def r427 : MobiusReciprocalTree := .branch r428 r429
private abbrev r431 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 86
private theorem rc431 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30080 r431 = true := by decide +kernel

private abbrev r432 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 87
private theorem rc432 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30144 r432 = true := by decide +kernel

private def r430 : MobiusReciprocalTree := .branch r431 r432
private def r426 : MobiusReciprocalTree := .branch r427 r430
private def r418 : MobiusReciprocalTree := .branch r419 r426
private abbrev r436 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 88
private theorem rc436 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30208 r436 = true := by decide +kernel

private abbrev r437 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 89
private theorem rc437 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30272 r437 = true := by decide +kernel

private def r435 : MobiusReciprocalTree := .branch r436 r437
private abbrev r439 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 90
private theorem rc439 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30336 r439 = true := by decide +kernel

private abbrev r440 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 91
private theorem rc440 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30400 r440 = true := by decide +kernel

private def r438 : MobiusReciprocalTree := .branch r439 r440
private def r434 : MobiusReciprocalTree := .branch r435 r438
private abbrev r443 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 92
private theorem rc443 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30464 r443 = true := by decide +kernel

private abbrev r444 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 93
private theorem rc444 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30528 r444 = true := by decide +kernel

private def r442 : MobiusReciprocalTree := .branch r443 r444
private abbrev r446 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 94
private theorem rc446 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30592 r446 = true := by decide +kernel

private abbrev r447 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 95
private theorem rc447 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30656 r447 = true := by decide +kernel

private def r445 : MobiusReciprocalTree := .branch r446 r447
private def r441 : MobiusReciprocalTree := .branch r442 r445
private def r433 : MobiusReciprocalTree := .branch r434 r441
private def r417 : MobiusReciprocalTree := .branch r418 r433
private def r385 : MobiusReciprocalTree := .branch r386 r417
private abbrev r453 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 96
private theorem rc453 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30720 r453 = true := by decide +kernel

private abbrev r454 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 97
private theorem rc454 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30784 r454 = true := by decide +kernel

private def r452 : MobiusReciprocalTree := .branch r453 r454
private abbrev r456 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 98
private theorem rc456 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30848 r456 = true := by decide +kernel

private abbrev r457 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 99
private theorem rc457 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30912 r457 = true := by decide +kernel

private def r455 : MobiusReciprocalTree := .branch r456 r457
private def r451 : MobiusReciprocalTree := .branch r452 r455
private abbrev r460 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 100
private theorem rc460 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30976 r460 = true := by decide +kernel

private abbrev r461 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 101
private theorem rc461 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31040 r461 = true := by decide +kernel

private def r459 : MobiusReciprocalTree := .branch r460 r461
private abbrev r463 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 102
private theorem rc463 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31104 r463 = true := by decide +kernel

private abbrev r464 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 103
private theorem rc464 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31168 r464 = true := by decide +kernel

private def r462 : MobiusReciprocalTree := .branch r463 r464
private def r458 : MobiusReciprocalTree := .branch r459 r462
private def r450 : MobiusReciprocalTree := .branch r451 r458
private abbrev r468 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 104
private theorem rc468 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31232 r468 = true := by decide +kernel

private abbrev r469 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 105
private theorem rc469 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31296 r469 = true := by decide +kernel

private def r467 : MobiusReciprocalTree := .branch r468 r469
private abbrev r471 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 106
private theorem rc471 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31360 r471 = true := by decide +kernel

private abbrev r472 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 107
private theorem rc472 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31424 r472 = true := by decide +kernel

private def r470 : MobiusReciprocalTree := .branch r471 r472
private def r466 : MobiusReciprocalTree := .branch r467 r470
private abbrev r475 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 108
private theorem rc475 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31488 r475 = true := by decide +kernel

private abbrev r476 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 109
private theorem rc476 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31552 r476 = true := by decide +kernel

private def r474 : MobiusReciprocalTree := .branch r475 r476
private abbrev r478 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 110
private theorem rc478 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31616 r478 = true := by decide +kernel

private abbrev r479 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 111
private theorem rc479 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31680 r479 = true := by decide +kernel

private def r477 : MobiusReciprocalTree := .branch r478 r479
private def r473 : MobiusReciprocalTree := .branch r474 r477
private def r465 : MobiusReciprocalTree := .branch r466 r473
private def r449 : MobiusReciprocalTree := .branch r450 r465
private abbrev r484 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 112
private theorem rc484 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31744 r484 = true := by decide +kernel

private abbrev r485 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 113
private theorem rc485 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31808 r485 = true := by decide +kernel

private def r483 : MobiusReciprocalTree := .branch r484 r485
private abbrev r487 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 114
private theorem rc487 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31872 r487 = true := by decide +kernel

private abbrev r488 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 115
private theorem rc488 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31936 r488 = true := by decide +kernel

private def r486 : MobiusReciprocalTree := .branch r487 r488
private def r482 : MobiusReciprocalTree := .branch r483 r486
private abbrev r491 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 116
private theorem rc491 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32000 r491 = true := by decide +kernel

private abbrev r492 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 117
private theorem rc492 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32064 r492 = true := by decide +kernel

private def r490 : MobiusReciprocalTree := .branch r491 r492
private abbrev r494 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 118
private theorem rc494 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32128 r494 = true := by decide +kernel

private abbrev r495 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 119
private theorem rc495 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32192 r495 = true := by decide +kernel

private def r493 : MobiusReciprocalTree := .branch r494 r495
private def r489 : MobiusReciprocalTree := .branch r490 r493
private def r481 : MobiusReciprocalTree := .branch r482 r489
private abbrev r499 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 120
private theorem rc499 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32256 r499 = true := by decide +kernel

private abbrev r500 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 121
private theorem rc500 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32320 r500 = true := by decide +kernel

private def r498 : MobiusReciprocalTree := .branch r499 r500
private abbrev r502 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 122
private theorem rc502 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32384 r502 = true := by decide +kernel

private abbrev r503 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 123
private theorem rc503 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32448 r503 = true := by decide +kernel

private def r501 : MobiusReciprocalTree := .branch r502 r503
private def r497 : MobiusReciprocalTree := .branch r498 r501
private abbrev r506 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 124
private theorem rc506 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32512 r506 = true := by decide +kernel

private abbrev r507 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 125
private theorem rc507 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32576 r507 = true := by decide +kernel

private def r505 : MobiusReciprocalTree := .branch r506 r507
private abbrev r509 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 126
private theorem rc509 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32640 r509 = true := by decide +kernel

private abbrev r510 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block003 127
private theorem rc510 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32704 r510 = true := by decide +kernel

private def r508 : MobiusReciprocalTree := .branch r509 r510
private def r504 : MobiusReciprocalTree := .branch r505 r508
private def r496 : MobiusReciprocalTree := .branch r497 r504
private def r480 : MobiusReciprocalTree := .branch r481 r496
private def r448 : MobiusReciprocalTree := .branch r449 r480
private def r384 : MobiusReciprocalTree := .branch r385 r448
private def r256 : MobiusReciprocalTree := .branch r257 r384
private def r0 : MobiusReciprocalTree := .branch r1 r256

theorem mobiusReciprocalSqrtPair001_checked_complete : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 16384 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block002 mobiusReciprocal1200001Block003) = true :=
  (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 8 16384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 7 16384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 6 16384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 16384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 16384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 16384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 16384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16384 _ _ (by decide) rc8 rc9 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16512 _ _ (by decide) rc11 rc12 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 16640 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16640 _ _ (by decide) rc15 rc16 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16768 _ _ (by decide) rc18 rc19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 16896 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 16896 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 16896 _ _ (by decide) rc23 rc24 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17024 _ _ (by decide) rc26 rc27 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 17152 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17152 _ _ (by decide) rc30 rc31 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17280 _ _ (by decide) rc33 rc34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 17408 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 17408 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 17408 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17408 _ _ (by decide) rc39 rc40 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17536 _ _ (by decide) rc42 rc43 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 17664 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17664 _ _ (by decide) rc46 rc47 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17792 _ _ (by decide) rc49 rc50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 17920 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 17920 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 17920 _ _ (by decide) rc54 rc55 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18048 _ _ (by decide) rc57 rc58 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 18176 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18176 _ _ (by decide) rc61 rc62 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18304 _ _ (by decide) rc64 rc65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 18432 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 18432 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 18432 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 18432 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18432 _ _ (by decide) rc71 rc72 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18560 _ _ (by decide) rc74 rc75 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 18688 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18688 _ _ (by decide) rc78 rc79 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18816 _ _ (by decide) rc81 rc82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 18944 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 18944 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 18944 _ _ (by decide) rc86 rc87 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19072 _ _ (by decide) rc89 rc90 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 19200 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19200 _ _ (by decide) rc93 rc94 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19328 _ _ (by decide) rc96 rc97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 19456 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 19456 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 19456 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19456 _ _ (by decide) rc102 rc103 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19584 _ _ (by decide) rc105 rc106 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 19712 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19712 _ _ (by decide) rc109 rc110 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19840 _ _ (by decide) rc112 rc113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 19968 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 19968 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 19968 _ _ (by decide) rc117 rc118 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20096 _ _ (by decide) rc120 rc121 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 20224 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20224 _ _ (by decide) rc124 rc125 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20352 _ _ (by decide) rc127 rc128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 6 20480 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 20480 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 20480 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 20480 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 20480 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20480 _ _ (by decide) rc135 rc136 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20608 _ _ (by decide) rc138 rc139 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 20736 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20736 _ _ (by decide) rc142 rc143 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20864 _ _ (by decide) rc145 rc146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 20992 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 20992 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 20992 _ _ (by decide) rc150 rc151 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21120 _ _ (by decide) rc153 rc154 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 21248 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21248 _ _ (by decide) rc157 rc158 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21376 _ _ (by decide) rc160 rc161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 21504 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 21504 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 21504 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21504 _ _ (by decide) rc166 rc167 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21632 _ _ (by decide) rc169 rc170 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 21760 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21760 _ _ (by decide) rc173 rc174 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 21888 _ _ (by decide) rc176 rc177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 22016 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 22016 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22016 _ _ (by decide) rc181 rc182 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22144 _ _ (by decide) rc184 rc185 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 22272 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22272 _ _ (by decide) rc188 rc189 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22400 _ _ (by decide) rc191 rc192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 22528 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 22528 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 22528 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 22528 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22528 _ _ (by decide) rc198 rc199 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22656 _ _ (by decide) rc201 rc202 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 22784 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22784 _ _ (by decide) rc205 rc206 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 22912 _ _ (by decide) rc208 rc209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 23040 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 23040 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23040 _ _ (by decide) rc213 rc214 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23168 _ _ (by decide) rc216 rc217 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 23296 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23296 _ _ (by decide) rc220 rc221 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23424 _ _ (by decide) rc223 rc224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 23552 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 23552 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 23552 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23552 _ _ (by decide) rc229 rc230 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23680 _ _ (by decide) rc232 rc233 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 23808 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23808 _ _ (by decide) rc236 rc237 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 23936 _ _ (by decide) rc239 rc240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 24064 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 24064 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24064 _ _ (by decide) rc244 rc245 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24192 _ _ (by decide) rc247 rc248 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 24320 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24320 _ _ (by decide) rc251 rc252 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24448 _ _ (by decide) rc254 rc255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 7 24576 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 6 24576 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 24576 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 24576 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 24576 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 24576 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24576 _ _ (by decide) rc263 rc264 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24704 _ _ (by decide) rc266 rc267 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 24832 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24832 _ _ (by decide) rc270 rc271 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 24960 _ _ (by decide) rc273 rc274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 25088 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 25088 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25088 _ _ (by decide) rc278 rc279 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25216 _ _ (by decide) rc281 rc282 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 25344 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25344 _ _ (by decide) rc285 rc286 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25472 _ _ (by decide) rc288 rc289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 25600 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 25600 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 25600 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25600 _ _ (by decide) rc294 rc295 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25728 _ _ (by decide) rc297 rc298 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 25856 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25856 _ _ (by decide) rc301 rc302 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 25984 _ _ (by decide) rc304 rc305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 26112 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 26112 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26112 _ _ (by decide) rc309 rc310 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26240 _ _ (by decide) rc312 rc313 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 26368 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26368 _ _ (by decide) rc316 rc317 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26496 _ _ (by decide) rc319 rc320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 26624 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 26624 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 26624 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 26624 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26624 _ _ (by decide) rc326 rc327 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26752 _ _ (by decide) rc329 rc330 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 26880 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 26880 _ _ (by decide) rc333 rc334 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27008 _ _ (by decide) rc336 rc337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 27136 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 27136 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27136 _ _ (by decide) rc341 rc342 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27264 _ _ (by decide) rc344 rc345 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 27392 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27392 _ _ (by decide) rc348 rc349 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27520 _ _ (by decide) rc351 rc352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 27648 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 27648 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 27648 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27648 _ _ (by decide) rc357 rc358 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27776 _ _ (by decide) rc360 rc361 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 27904 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 27904 _ _ (by decide) rc364 rc365 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28032 _ _ (by decide) rc367 rc368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 28160 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 28160 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28160 _ _ (by decide) rc372 rc373 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28288 _ _ (by decide) rc375 rc376 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 28416 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28416 _ _ (by decide) rc379 rc380 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28544 _ _ (by decide) rc382 rc383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 6 28672 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 28672 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 28672 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 28672 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 28672 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28672 _ _ (by decide) rc390 rc391 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28800 _ _ (by decide) rc393 rc394 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 28928 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 28928 _ _ (by decide) rc397 rc398 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29056 _ _ (by decide) rc400 rc401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 29184 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 29184 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29184 _ _ (by decide) rc405 rc406 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29312 _ _ (by decide) rc408 rc409 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 29440 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29440 _ _ (by decide) rc412 rc413 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29568 _ _ (by decide) rc415 rc416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 29696 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 29696 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 29696 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29696 _ _ (by decide) rc421 rc422 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29824 _ _ (by decide) rc424 rc425 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 29952 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 29952 _ _ (by decide) rc428 rc429 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30080 _ _ (by decide) rc431 rc432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 30208 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 30208 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30208 _ _ (by decide) rc436 rc437 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30336 _ _ (by decide) rc439 rc440 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 30464 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30464 _ _ (by decide) rc443 rc444 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30592 _ _ (by decide) rc446 rc447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 30720 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 30720 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 30720 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 30720 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30720 _ _ (by decide) rc453 rc454 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30848 _ _ (by decide) rc456 rc457 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 30976 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 30976 _ _ (by decide) rc460 rc461 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31104 _ _ (by decide) rc463 rc464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 31232 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 31232 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31232 _ _ (by decide) rc468 rc469 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31360 _ _ (by decide) rc471 rc472 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 31488 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31488 _ _ (by decide) rc475 rc476 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31616 _ _ (by decide) rc478 rc479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 31744 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 31744 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 31744 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31744 _ _ (by decide) rc484 rc485 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 31872 _ _ (by decide) rc487 rc488 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 32000 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32000 _ _ (by decide) rc491 rc492 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32128 _ _ (by decide) rc494 rc495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 32256 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 32256 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32256 _ _ (by decide) rc499 rc500 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32384 _ _ (by decide) rc502 rc503 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 32512 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32512 _ _ (by decide) rc506 rc507 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 32640 _ _ (by decide) rc509 rc510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott
end

open Helfgott
theorem solution : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 16384 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block002 mobiusReciprocal1200001Block003) = true := Helfgott.mobiusReciprocalSqrtPair001_checked_complete
#print axioms solution
