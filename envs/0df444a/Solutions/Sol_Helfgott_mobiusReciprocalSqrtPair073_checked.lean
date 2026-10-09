-- Prove2me | solution 1 for Helfgott.mobiusReciprocalSqrtPair073_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T05:46:17.107795+00:00
-- url     : https://prove2.me/submissions/e781814e-c4ff-4617-a44d-313bb60d511a

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part18
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

private abbrev r8 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 0
private theorem rc8 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196032 r8 = true := by decide +kernel

private abbrev r9 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 1
private theorem rc9 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196096 r9 = true := by decide +kernel

private def r7 : MobiusReciprocalTree := .branch r8 r9
private abbrev r11 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 2
private theorem rc11 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196160 r11 = true := by decide +kernel

private abbrev r12 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 3
private theorem rc12 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196224 r12 = true := by decide +kernel

private def r10 : MobiusReciprocalTree := .branch r11 r12
private def r6 : MobiusReciprocalTree := .branch r7 r10
private abbrev r15 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 4
private theorem rc15 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196288 r15 = true := by decide +kernel

private abbrev r16 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 5
private theorem rc16 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196352 r16 = true := by decide +kernel

private def r14 : MobiusReciprocalTree := .branch r15 r16
private abbrev r18 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 6
private theorem rc18 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196416 r18 = true := by decide +kernel

private abbrev r19 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 7
private theorem rc19 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196480 r19 = true := by decide +kernel

private def r17 : MobiusReciprocalTree := .branch r18 r19
private def r13 : MobiusReciprocalTree := .branch r14 r17
private def r5 : MobiusReciprocalTree := .branch r6 r13
private abbrev r23 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 8
private theorem rc23 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196544 r23 = true := by decide +kernel

private abbrev r24 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 9
private theorem rc24 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196608 r24 = true := by decide +kernel

private def r22 : MobiusReciprocalTree := .branch r23 r24
private abbrev r26 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 10
private theorem rc26 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196672 r26 = true := by decide +kernel

private abbrev r27 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 11
private theorem rc27 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196736 r27 = true := by decide +kernel

private def r25 : MobiusReciprocalTree := .branch r26 r27
private def r21 : MobiusReciprocalTree := .branch r22 r25
private abbrev r30 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 12
private theorem rc30 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196800 r30 = true := by decide +kernel

private abbrev r31 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 13
private theorem rc31 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196864 r31 = true := by decide +kernel

private def r29 : MobiusReciprocalTree := .branch r30 r31
private abbrev r33 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 14
private theorem rc33 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196928 r33 = true := by decide +kernel

private abbrev r34 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 15
private theorem rc34 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196992 r34 = true := by decide +kernel

private def r32 : MobiusReciprocalTree := .branch r33 r34
private def r28 : MobiusReciprocalTree := .branch r29 r32
private def r20 : MobiusReciprocalTree := .branch r21 r28
private def r4 : MobiusReciprocalTree := .branch r5 r20
private abbrev r39 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 16
private theorem rc39 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197056 r39 = true := by decide +kernel

private abbrev r40 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 17
private theorem rc40 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197120 r40 = true := by decide +kernel

private def r38 : MobiusReciprocalTree := .branch r39 r40
private abbrev r42 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 18
private theorem rc42 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197184 r42 = true := by decide +kernel

private abbrev r43 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 19
private theorem rc43 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197248 r43 = true := by decide +kernel

private def r41 : MobiusReciprocalTree := .branch r42 r43
private def r37 : MobiusReciprocalTree := .branch r38 r41
private abbrev r46 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 20
private theorem rc46 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197312 r46 = true := by decide +kernel

private abbrev r47 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 21
private theorem rc47 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197376 r47 = true := by decide +kernel

private def r45 : MobiusReciprocalTree := .branch r46 r47
private abbrev r49 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 22
private theorem rc49 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197440 r49 = true := by decide +kernel

private abbrev r50 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 23
private theorem rc50 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197504 r50 = true := by decide +kernel

private def r48 : MobiusReciprocalTree := .branch r49 r50
private def r44 : MobiusReciprocalTree := .branch r45 r48
private def r36 : MobiusReciprocalTree := .branch r37 r44
private abbrev r54 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 24
private theorem rc54 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197568 r54 = true := by decide +kernel

private abbrev r55 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 25
private theorem rc55 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197632 r55 = true := by decide +kernel

private def r53 : MobiusReciprocalTree := .branch r54 r55
private abbrev r57 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 26
private theorem rc57 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197696 r57 = true := by decide +kernel

private abbrev r58 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 27
private theorem rc58 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197760 r58 = true := by decide +kernel

private def r56 : MobiusReciprocalTree := .branch r57 r58
private def r52 : MobiusReciprocalTree := .branch r53 r56
private abbrev r61 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 28
private theorem rc61 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197824 r61 = true := by decide +kernel

private abbrev r62 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 29
private theorem rc62 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197888 r62 = true := by decide +kernel

private def r60 : MobiusReciprocalTree := .branch r61 r62
private abbrev r64 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 30
private theorem rc64 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197952 r64 = true := by decide +kernel

private abbrev r65 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 31
private theorem rc65 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198016 r65 = true := by decide +kernel

private def r63 : MobiusReciprocalTree := .branch r64 r65
private def r59 : MobiusReciprocalTree := .branch r60 r63
private def r51 : MobiusReciprocalTree := .branch r52 r59
private def r35 : MobiusReciprocalTree := .branch r36 r51
private def r3 : MobiusReciprocalTree := .branch r4 r35
private abbrev r71 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 32
private theorem rc71 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198080 r71 = true := by decide +kernel

private abbrev r72 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 33
private theorem rc72 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198144 r72 = true := by decide +kernel

private def r70 : MobiusReciprocalTree := .branch r71 r72
private abbrev r74 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 34
private theorem rc74 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198208 r74 = true := by decide +kernel

private abbrev r75 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 35
private theorem rc75 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198272 r75 = true := by decide +kernel

private def r73 : MobiusReciprocalTree := .branch r74 r75
private def r69 : MobiusReciprocalTree := .branch r70 r73
private abbrev r78 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 36
private theorem rc78 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198336 r78 = true := by decide +kernel

private abbrev r79 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 37
private theorem rc79 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198400 r79 = true := by decide +kernel

private def r77 : MobiusReciprocalTree := .branch r78 r79
private abbrev r81 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 38
private theorem rc81 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198464 r81 = true := by decide +kernel

private abbrev r82 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 39
private theorem rc82 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198528 r82 = true := by decide +kernel

private def r80 : MobiusReciprocalTree := .branch r81 r82
private def r76 : MobiusReciprocalTree := .branch r77 r80
private def r68 : MobiusReciprocalTree := .branch r69 r76
private abbrev r86 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 40
private theorem rc86 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198592 r86 = true := by decide +kernel

private abbrev r87 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 41
private theorem rc87 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198656 r87 = true := by decide +kernel

private def r85 : MobiusReciprocalTree := .branch r86 r87
private abbrev r89 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 42
private theorem rc89 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198720 r89 = true := by decide +kernel

private abbrev r90 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 43
private theorem rc90 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198784 r90 = true := by decide +kernel

private def r88 : MobiusReciprocalTree := .branch r89 r90
private def r84 : MobiusReciprocalTree := .branch r85 r88
private abbrev r93 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 44
private theorem rc93 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198848 r93 = true := by decide +kernel

private abbrev r94 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 45
private theorem rc94 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198912 r94 = true := by decide +kernel

private def r92 : MobiusReciprocalTree := .branch r93 r94
private abbrev r96 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 46
private theorem rc96 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198976 r96 = true := by decide +kernel

private abbrev r97 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 47
private theorem rc97 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199040 r97 = true := by decide +kernel

private def r95 : MobiusReciprocalTree := .branch r96 r97
private def r91 : MobiusReciprocalTree := .branch r92 r95
private def r83 : MobiusReciprocalTree := .branch r84 r91
private def r67 : MobiusReciprocalTree := .branch r68 r83
private abbrev r102 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 48
private theorem rc102 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199104 r102 = true := by decide +kernel

private abbrev r103 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 49
private theorem rc103 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199168 r103 = true := by decide +kernel

private def r101 : MobiusReciprocalTree := .branch r102 r103
private abbrev r105 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 50
private theorem rc105 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199232 r105 = true := by decide +kernel

private abbrev r106 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 51
private theorem rc106 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199296 r106 = true := by decide +kernel

private def r104 : MobiusReciprocalTree := .branch r105 r106
private def r100 : MobiusReciprocalTree := .branch r101 r104
private abbrev r109 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 52
private theorem rc109 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199360 r109 = true := by decide +kernel

private abbrev r110 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 53
private theorem rc110 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199424 r110 = true := by decide +kernel

private def r108 : MobiusReciprocalTree := .branch r109 r110
private abbrev r112 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 54
private theorem rc112 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199488 r112 = true := by decide +kernel

private abbrev r113 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 55
private theorem rc113 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199552 r113 = true := by decide +kernel

private def r111 : MobiusReciprocalTree := .branch r112 r113
private def r107 : MobiusReciprocalTree := .branch r108 r111
private def r99 : MobiusReciprocalTree := .branch r100 r107
private abbrev r117 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 56
private theorem rc117 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199616 r117 = true := by decide +kernel

private abbrev r118 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 57
private theorem rc118 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199680 r118 = true := by decide +kernel

private def r116 : MobiusReciprocalTree := .branch r117 r118
private abbrev r120 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 58
private theorem rc120 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199744 r120 = true := by decide +kernel

private abbrev r121 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 59
private theorem rc121 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199808 r121 = true := by decide +kernel

private def r119 : MobiusReciprocalTree := .branch r120 r121
private def r115 : MobiusReciprocalTree := .branch r116 r119
private abbrev r124 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 60
private theorem rc124 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199872 r124 = true := by decide +kernel

private abbrev r125 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 61
private theorem rc125 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199936 r125 = true := by decide +kernel

private def r123 : MobiusReciprocalTree := .branch r124 r125
private abbrev r127 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block146 62
private theorem rc127 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1200000 r127 = true := by decide +kernel

private abbrev r128 : MobiusReciprocalTree := (MobiusReciprocalTree.leaf (-119400916) (-119400916) 0 0)
private theorem rc128 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1200064 r128 = true := by decide +kernel

private def r126 : MobiusReciprocalTree := .branch r127 r128
private def r122 : MobiusReciprocalTree := .branch r123 r126
private def r114 : MobiusReciprocalTree := .branch r115 r122
private def r98 : MobiusReciprocalTree := .branch r99 r114
private def r66 : MobiusReciprocalTree := .branch r67 r98
private def r2 : MobiusReciprocalTree := .branch r3 r66
private abbrev r129 : MobiusReciprocalTree := (MobiusReciprocalTree.leaf (-119400916) (-119400916) 0 0)
private theorem rc129 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 7 1200128 r129 = true := by decide +kernel

private def r1 : MobiusReciprocalTree := .branch r2 r129
private abbrev r130 : MobiusReciprocalTree := (MobiusReciprocalTree.leaf (-119400916) (-119400916) 0 0)
private theorem rc130 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 8 1204224 r130 = true := by decide +kernel

private def r0 : MobiusReciprocalTree := .branch r1 r130

theorem mobiusReciprocalSqrtPair073_checked_complete : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1196032 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block146 (MobiusReciprocalTree.leaf (-119400916) (-119400916) 0 0)) = true :=
  (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 8 1196032 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 7 1196032 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 6 1196032 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 1196032 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 1196032 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 1196032 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1196032 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196032 _ _ (by decide) rc8 rc9 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196160 _ _ (by decide) rc11 rc12 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1196288 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196288 _ _ (by decide) rc15 rc16 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196416 _ _ (by decide) rc18 rc19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 1196544 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1196544 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196544 _ _ (by decide) rc23 rc24 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196672 _ _ (by decide) rc26 rc27 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1196800 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196800 _ _ (by decide) rc30 rc31 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1196928 _ _ (by decide) rc33 rc34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 1197056 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 1197056 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1197056 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197056 _ _ (by decide) rc39 rc40 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197184 _ _ (by decide) rc42 rc43 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1197312 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197312 _ _ (by decide) rc46 rc47 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197440 _ _ (by decide) rc49 rc50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 1197568 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1197568 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197568 _ _ (by decide) rc54 rc55 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197696 _ _ (by decide) rc57 rc58 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1197824 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197824 _ _ (by decide) rc61 rc62 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1197952 _ _ (by decide) rc64 rc65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 1198080 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 1198080 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 1198080 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1198080 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198080 _ _ (by decide) rc71 rc72 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198208 _ _ (by decide) rc74 rc75 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1198336 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198336 _ _ (by decide) rc78 rc79 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198464 _ _ (by decide) rc81 rc82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 1198592 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1198592 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198592 _ _ (by decide) rc86 rc87 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198720 _ _ (by decide) rc89 rc90 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1198848 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198848 _ _ (by decide) rc93 rc94 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1198976 _ _ (by decide) rc96 rc97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 1199104 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 1199104 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1199104 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199104 _ _ (by decide) rc102 rc103 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199232 _ _ (by decide) rc105 rc106 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1199360 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199360 _ _ (by decide) rc109 rc110 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199488 _ _ (by decide) rc112 rc113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 1199616 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1199616 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199616 _ _ (by decide) rc117 rc118 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199744 _ _ (by decide) rc120 rc121 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 1199872 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1199872 _ _ (by decide) rc124 rc125 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 1200000 _ _ (by decide) rc127 rc128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) rc129 (by decide +kernel)) rc130 (by decide +kernel))

end Helfgott
end

open Helfgott
theorem solution : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 1196032 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block146 (MobiusReciprocalTree.leaf (-119400916) (-119400916) 0 0)) = true := Helfgott.mobiusReciprocalSqrtPair073_checked_complete
#print axioms solution
