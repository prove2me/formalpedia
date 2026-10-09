-- Prove2me | solution 1 for Helfgott.mobiusReciprocalSqrtPair016_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T04:44:26.454122+00:00
-- url     : https://prove2.me/submissions/fb493ae5-a386-4c80-8ddf-cdd020666e46

import Definitions.Def_Helfgott_MobiusFiniteTable1200001
import Definitions.Def_Helfgott_MobiusReciprocalTable1200001_Part04
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

private abbrev r8 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 0
private theorem rc8 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262144 r8 = true := by decide +kernel

private abbrev r9 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 1
private theorem rc9 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262208 r9 = true := by decide +kernel

private def r7 : MobiusReciprocalTree := .branch r8 r9
private abbrev r11 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 2
private theorem rc11 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262272 r11 = true := by decide +kernel

private abbrev r12 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 3
private theorem rc12 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262336 r12 = true := by decide +kernel

private def r10 : MobiusReciprocalTree := .branch r11 r12
private def r6 : MobiusReciprocalTree := .branch r7 r10
private abbrev r15 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 4
private theorem rc15 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262400 r15 = true := by decide +kernel

private abbrev r16 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 5
private theorem rc16 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262464 r16 = true := by decide +kernel

private def r14 : MobiusReciprocalTree := .branch r15 r16
private abbrev r18 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 6
private theorem rc18 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262528 r18 = true := by decide +kernel

private abbrev r19 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 7
private theorem rc19 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262592 r19 = true := by decide +kernel

private def r17 : MobiusReciprocalTree := .branch r18 r19
private def r13 : MobiusReciprocalTree := .branch r14 r17
private def r5 : MobiusReciprocalTree := .branch r6 r13
private abbrev r23 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 8
private theorem rc23 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262656 r23 = true := by decide +kernel

private abbrev r24 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 9
private theorem rc24 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262720 r24 = true := by decide +kernel

private def r22 : MobiusReciprocalTree := .branch r23 r24
private abbrev r26 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 10
private theorem rc26 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262784 r26 = true := by decide +kernel

private abbrev r27 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 11
private theorem rc27 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262848 r27 = true := by decide +kernel

private def r25 : MobiusReciprocalTree := .branch r26 r27
private def r21 : MobiusReciprocalTree := .branch r22 r25
private abbrev r30 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 12
private theorem rc30 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262912 r30 = true := by decide +kernel

private abbrev r31 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 13
private theorem rc31 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262976 r31 = true := by decide +kernel

private def r29 : MobiusReciprocalTree := .branch r30 r31
private abbrev r33 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 14
private theorem rc33 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263040 r33 = true := by decide +kernel

private abbrev r34 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 15
private theorem rc34 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263104 r34 = true := by decide +kernel

private def r32 : MobiusReciprocalTree := .branch r33 r34
private def r28 : MobiusReciprocalTree := .branch r29 r32
private def r20 : MobiusReciprocalTree := .branch r21 r28
private def r4 : MobiusReciprocalTree := .branch r5 r20
private abbrev r39 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 16
private theorem rc39 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263168 r39 = true := by decide +kernel

private abbrev r40 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 17
private theorem rc40 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263232 r40 = true := by decide +kernel

private def r38 : MobiusReciprocalTree := .branch r39 r40
private abbrev r42 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 18
private theorem rc42 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263296 r42 = true := by decide +kernel

private abbrev r43 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 19
private theorem rc43 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263360 r43 = true := by decide +kernel

private def r41 : MobiusReciprocalTree := .branch r42 r43
private def r37 : MobiusReciprocalTree := .branch r38 r41
private abbrev r46 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 20
private theorem rc46 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263424 r46 = true := by decide +kernel

private abbrev r47 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 21
private theorem rc47 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263488 r47 = true := by decide +kernel

private def r45 : MobiusReciprocalTree := .branch r46 r47
private abbrev r49 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 22
private theorem rc49 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263552 r49 = true := by decide +kernel

private abbrev r50 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 23
private theorem rc50 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263616 r50 = true := by decide +kernel

private def r48 : MobiusReciprocalTree := .branch r49 r50
private def r44 : MobiusReciprocalTree := .branch r45 r48
private def r36 : MobiusReciprocalTree := .branch r37 r44
private abbrev r54 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 24
private theorem rc54 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263680 r54 = true := by decide +kernel

private abbrev r55 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 25
private theorem rc55 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263744 r55 = true := by decide +kernel

private def r53 : MobiusReciprocalTree := .branch r54 r55
private abbrev r57 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 26
private theorem rc57 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263808 r57 = true := by decide +kernel

private abbrev r58 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 27
private theorem rc58 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263872 r58 = true := by decide +kernel

private def r56 : MobiusReciprocalTree := .branch r57 r58
private def r52 : MobiusReciprocalTree := .branch r53 r56
private abbrev r61 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 28
private theorem rc61 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263936 r61 = true := by decide +kernel

private abbrev r62 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 29
private theorem rc62 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264000 r62 = true := by decide +kernel

private def r60 : MobiusReciprocalTree := .branch r61 r62
private abbrev r64 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 30
private theorem rc64 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264064 r64 = true := by decide +kernel

private abbrev r65 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 31
private theorem rc65 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264128 r65 = true := by decide +kernel

private def r63 : MobiusReciprocalTree := .branch r64 r65
private def r59 : MobiusReciprocalTree := .branch r60 r63
private def r51 : MobiusReciprocalTree := .branch r52 r59
private def r35 : MobiusReciprocalTree := .branch r36 r51
private def r3 : MobiusReciprocalTree := .branch r4 r35
private abbrev r71 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 32
private theorem rc71 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264192 r71 = true := by decide +kernel

private abbrev r72 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 33
private theorem rc72 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264256 r72 = true := by decide +kernel

private def r70 : MobiusReciprocalTree := .branch r71 r72
private abbrev r74 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 34
private theorem rc74 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264320 r74 = true := by decide +kernel

private abbrev r75 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 35
private theorem rc75 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264384 r75 = true := by decide +kernel

private def r73 : MobiusReciprocalTree := .branch r74 r75
private def r69 : MobiusReciprocalTree := .branch r70 r73
private abbrev r78 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 36
private theorem rc78 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264448 r78 = true := by decide +kernel

private abbrev r79 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 37
private theorem rc79 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264512 r79 = true := by decide +kernel

private def r77 : MobiusReciprocalTree := .branch r78 r79
private abbrev r81 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 38
private theorem rc81 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264576 r81 = true := by decide +kernel

private abbrev r82 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 39
private theorem rc82 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264640 r82 = true := by decide +kernel

private def r80 : MobiusReciprocalTree := .branch r81 r82
private def r76 : MobiusReciprocalTree := .branch r77 r80
private def r68 : MobiusReciprocalTree := .branch r69 r76
private abbrev r86 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 40
private theorem rc86 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264704 r86 = true := by decide +kernel

private abbrev r87 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 41
private theorem rc87 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264768 r87 = true := by decide +kernel

private def r85 : MobiusReciprocalTree := .branch r86 r87
private abbrev r89 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 42
private theorem rc89 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264832 r89 = true := by decide +kernel

private abbrev r90 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 43
private theorem rc90 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264896 r90 = true := by decide +kernel

private def r88 : MobiusReciprocalTree := .branch r89 r90
private def r84 : MobiusReciprocalTree := .branch r85 r88
private abbrev r93 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 44
private theorem rc93 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264960 r93 = true := by decide +kernel

private abbrev r94 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 45
private theorem rc94 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265024 r94 = true := by decide +kernel

private def r92 : MobiusReciprocalTree := .branch r93 r94
private abbrev r96 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 46
private theorem rc96 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265088 r96 = true := by decide +kernel

private abbrev r97 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 47
private theorem rc97 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265152 r97 = true := by decide +kernel

private def r95 : MobiusReciprocalTree := .branch r96 r97
private def r91 : MobiusReciprocalTree := .branch r92 r95
private def r83 : MobiusReciprocalTree := .branch r84 r91
private def r67 : MobiusReciprocalTree := .branch r68 r83
private abbrev r102 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 48
private theorem rc102 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265216 r102 = true := by decide +kernel

private abbrev r103 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 49
private theorem rc103 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265280 r103 = true := by decide +kernel

private def r101 : MobiusReciprocalTree := .branch r102 r103
private abbrev r105 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 50
private theorem rc105 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265344 r105 = true := by decide +kernel

private abbrev r106 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 51
private theorem rc106 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265408 r106 = true := by decide +kernel

private def r104 : MobiusReciprocalTree := .branch r105 r106
private def r100 : MobiusReciprocalTree := .branch r101 r104
private abbrev r109 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 52
private theorem rc109 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265472 r109 = true := by decide +kernel

private abbrev r110 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 53
private theorem rc110 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265536 r110 = true := by decide +kernel

private def r108 : MobiusReciprocalTree := .branch r109 r110
private abbrev r112 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 54
private theorem rc112 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265600 r112 = true := by decide +kernel

private abbrev r113 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 55
private theorem rc113 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265664 r113 = true := by decide +kernel

private def r111 : MobiusReciprocalTree := .branch r112 r113
private def r107 : MobiusReciprocalTree := .branch r108 r111
private def r99 : MobiusReciprocalTree := .branch r100 r107
private abbrev r117 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 56
private theorem rc117 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265728 r117 = true := by decide +kernel

private abbrev r118 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 57
private theorem rc118 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265792 r118 = true := by decide +kernel

private def r116 : MobiusReciprocalTree := .branch r117 r118
private abbrev r120 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 58
private theorem rc120 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265856 r120 = true := by decide +kernel

private abbrev r121 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 59
private theorem rc121 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265920 r121 = true := by decide +kernel

private def r119 : MobiusReciprocalTree := .branch r120 r121
private def r115 : MobiusReciprocalTree := .branch r116 r119
private abbrev r124 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 60
private theorem rc124 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265984 r124 = true := by decide +kernel

private abbrev r125 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 61
private theorem rc125 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266048 r125 = true := by decide +kernel

private def r123 : MobiusReciprocalTree := .branch r124 r125
private abbrev r127 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 62
private theorem rc127 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266112 r127 = true := by decide +kernel

private abbrev r128 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 63
private theorem rc128 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266176 r128 = true := by decide +kernel

private def r126 : MobiusReciprocalTree := .branch r127 r128
private def r122 : MobiusReciprocalTree := .branch r123 r126
private def r114 : MobiusReciprocalTree := .branch r115 r122
private def r98 : MobiusReciprocalTree := .branch r99 r114
private def r66 : MobiusReciprocalTree := .branch r67 r98
private def r2 : MobiusReciprocalTree := .branch r3 r66
private abbrev r135 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 64
private theorem rc135 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266240 r135 = true := by decide +kernel

private abbrev r136 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 65
private theorem rc136 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266304 r136 = true := by decide +kernel

private def r134 : MobiusReciprocalTree := .branch r135 r136
private abbrev r138 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 66
private theorem rc138 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266368 r138 = true := by decide +kernel

private abbrev r139 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 67
private theorem rc139 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266432 r139 = true := by decide +kernel

private def r137 : MobiusReciprocalTree := .branch r138 r139
private def r133 : MobiusReciprocalTree := .branch r134 r137
private abbrev r142 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 68
private theorem rc142 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266496 r142 = true := by decide +kernel

private abbrev r143 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 69
private theorem rc143 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266560 r143 = true := by decide +kernel

private def r141 : MobiusReciprocalTree := .branch r142 r143
private abbrev r145 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 70
private theorem rc145 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266624 r145 = true := by decide +kernel

private abbrev r146 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 71
private theorem rc146 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266688 r146 = true := by decide +kernel

private def r144 : MobiusReciprocalTree := .branch r145 r146
private def r140 : MobiusReciprocalTree := .branch r141 r144
private def r132 : MobiusReciprocalTree := .branch r133 r140
private abbrev r150 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 72
private theorem rc150 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266752 r150 = true := by decide +kernel

private abbrev r151 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 73
private theorem rc151 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266816 r151 = true := by decide +kernel

private def r149 : MobiusReciprocalTree := .branch r150 r151
private abbrev r153 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 74
private theorem rc153 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266880 r153 = true := by decide +kernel

private abbrev r154 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 75
private theorem rc154 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266944 r154 = true := by decide +kernel

private def r152 : MobiusReciprocalTree := .branch r153 r154
private def r148 : MobiusReciprocalTree := .branch r149 r152
private abbrev r157 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 76
private theorem rc157 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267008 r157 = true := by decide +kernel

private abbrev r158 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 77
private theorem rc158 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267072 r158 = true := by decide +kernel

private def r156 : MobiusReciprocalTree := .branch r157 r158
private abbrev r160 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 78
private theorem rc160 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267136 r160 = true := by decide +kernel

private abbrev r161 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 79
private theorem rc161 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267200 r161 = true := by decide +kernel

private def r159 : MobiusReciprocalTree := .branch r160 r161
private def r155 : MobiusReciprocalTree := .branch r156 r159
private def r147 : MobiusReciprocalTree := .branch r148 r155
private def r131 : MobiusReciprocalTree := .branch r132 r147
private abbrev r166 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 80
private theorem rc166 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267264 r166 = true := by decide +kernel

private abbrev r167 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 81
private theorem rc167 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267328 r167 = true := by decide +kernel

private def r165 : MobiusReciprocalTree := .branch r166 r167
private abbrev r169 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 82
private theorem rc169 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267392 r169 = true := by decide +kernel

private abbrev r170 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 83
private theorem rc170 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267456 r170 = true := by decide +kernel

private def r168 : MobiusReciprocalTree := .branch r169 r170
private def r164 : MobiusReciprocalTree := .branch r165 r168
private abbrev r173 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 84
private theorem rc173 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267520 r173 = true := by decide +kernel

private abbrev r174 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 85
private theorem rc174 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267584 r174 = true := by decide +kernel

private def r172 : MobiusReciprocalTree := .branch r173 r174
private abbrev r176 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 86
private theorem rc176 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267648 r176 = true := by decide +kernel

private abbrev r177 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 87
private theorem rc177 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267712 r177 = true := by decide +kernel

private def r175 : MobiusReciprocalTree := .branch r176 r177
private def r171 : MobiusReciprocalTree := .branch r172 r175
private def r163 : MobiusReciprocalTree := .branch r164 r171
private abbrev r181 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 88
private theorem rc181 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267776 r181 = true := by decide +kernel

private abbrev r182 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 89
private theorem rc182 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267840 r182 = true := by decide +kernel

private def r180 : MobiusReciprocalTree := .branch r181 r182
private abbrev r184 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 90
private theorem rc184 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267904 r184 = true := by decide +kernel

private abbrev r185 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 91
private theorem rc185 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267968 r185 = true := by decide +kernel

private def r183 : MobiusReciprocalTree := .branch r184 r185
private def r179 : MobiusReciprocalTree := .branch r180 r183
private abbrev r188 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 92
private theorem rc188 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268032 r188 = true := by decide +kernel

private abbrev r189 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 93
private theorem rc189 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268096 r189 = true := by decide +kernel

private def r187 : MobiusReciprocalTree := .branch r188 r189
private abbrev r191 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 94
private theorem rc191 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268160 r191 = true := by decide +kernel

private abbrev r192 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 95
private theorem rc192 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268224 r192 = true := by decide +kernel

private def r190 : MobiusReciprocalTree := .branch r191 r192
private def r186 : MobiusReciprocalTree := .branch r187 r190
private def r178 : MobiusReciprocalTree := .branch r179 r186
private def r162 : MobiusReciprocalTree := .branch r163 r178
private def r130 : MobiusReciprocalTree := .branch r131 r162
private abbrev r198 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 96
private theorem rc198 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268288 r198 = true := by decide +kernel

private abbrev r199 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 97
private theorem rc199 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268352 r199 = true := by decide +kernel

private def r197 : MobiusReciprocalTree := .branch r198 r199
private abbrev r201 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 98
private theorem rc201 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268416 r201 = true := by decide +kernel

private abbrev r202 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 99
private theorem rc202 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268480 r202 = true := by decide +kernel

private def r200 : MobiusReciprocalTree := .branch r201 r202
private def r196 : MobiusReciprocalTree := .branch r197 r200
private abbrev r205 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 100
private theorem rc205 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268544 r205 = true := by decide +kernel

private abbrev r206 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 101
private theorem rc206 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268608 r206 = true := by decide +kernel

private def r204 : MobiusReciprocalTree := .branch r205 r206
private abbrev r208 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 102
private theorem rc208 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268672 r208 = true := by decide +kernel

private abbrev r209 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 103
private theorem rc209 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268736 r209 = true := by decide +kernel

private def r207 : MobiusReciprocalTree := .branch r208 r209
private def r203 : MobiusReciprocalTree := .branch r204 r207
private def r195 : MobiusReciprocalTree := .branch r196 r203
private abbrev r213 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 104
private theorem rc213 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268800 r213 = true := by decide +kernel

private abbrev r214 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 105
private theorem rc214 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268864 r214 = true := by decide +kernel

private def r212 : MobiusReciprocalTree := .branch r213 r214
private abbrev r216 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 106
private theorem rc216 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268928 r216 = true := by decide +kernel

private abbrev r217 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 107
private theorem rc217 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268992 r217 = true := by decide +kernel

private def r215 : MobiusReciprocalTree := .branch r216 r217
private def r211 : MobiusReciprocalTree := .branch r212 r215
private abbrev r220 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 108
private theorem rc220 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269056 r220 = true := by decide +kernel

private abbrev r221 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 109
private theorem rc221 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269120 r221 = true := by decide +kernel

private def r219 : MobiusReciprocalTree := .branch r220 r221
private abbrev r223 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 110
private theorem rc223 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269184 r223 = true := by decide +kernel

private abbrev r224 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 111
private theorem rc224 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269248 r224 = true := by decide +kernel

private def r222 : MobiusReciprocalTree := .branch r223 r224
private def r218 : MobiusReciprocalTree := .branch r219 r222
private def r210 : MobiusReciprocalTree := .branch r211 r218
private def r194 : MobiusReciprocalTree := .branch r195 r210
private abbrev r229 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 112
private theorem rc229 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269312 r229 = true := by decide +kernel

private abbrev r230 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 113
private theorem rc230 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269376 r230 = true := by decide +kernel

private def r228 : MobiusReciprocalTree := .branch r229 r230
private abbrev r232 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 114
private theorem rc232 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269440 r232 = true := by decide +kernel

private abbrev r233 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 115
private theorem rc233 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269504 r233 = true := by decide +kernel

private def r231 : MobiusReciprocalTree := .branch r232 r233
private def r227 : MobiusReciprocalTree := .branch r228 r231
private abbrev r236 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 116
private theorem rc236 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269568 r236 = true := by decide +kernel

private abbrev r237 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 117
private theorem rc237 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269632 r237 = true := by decide +kernel

private def r235 : MobiusReciprocalTree := .branch r236 r237
private abbrev r239 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 118
private theorem rc239 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269696 r239 = true := by decide +kernel

private abbrev r240 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 119
private theorem rc240 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269760 r240 = true := by decide +kernel

private def r238 : MobiusReciprocalTree := .branch r239 r240
private def r234 : MobiusReciprocalTree := .branch r235 r238
private def r226 : MobiusReciprocalTree := .branch r227 r234
private abbrev r244 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 120
private theorem rc244 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269824 r244 = true := by decide +kernel

private abbrev r245 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 121
private theorem rc245 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269888 r245 = true := by decide +kernel

private def r243 : MobiusReciprocalTree := .branch r244 r245
private abbrev r247 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 122
private theorem rc247 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269952 r247 = true := by decide +kernel

private abbrev r248 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 123
private theorem rc248 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270016 r248 = true := by decide +kernel

private def r246 : MobiusReciprocalTree := .branch r247 r248
private def r242 : MobiusReciprocalTree := .branch r243 r246
private abbrev r251 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 124
private theorem rc251 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270080 r251 = true := by decide +kernel

private abbrev r252 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 125
private theorem rc252 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270144 r252 = true := by decide +kernel

private def r250 : MobiusReciprocalTree := .branch r251 r252
private abbrev r254 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 126
private theorem rc254 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270208 r254 = true := by decide +kernel

private abbrev r255 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block032 127
private theorem rc255 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270272 r255 = true := by decide +kernel

private def r253 : MobiusReciprocalTree := .branch r254 r255
private def r249 : MobiusReciprocalTree := .branch r250 r253
private def r241 : MobiusReciprocalTree := .branch r242 r249
private def r225 : MobiusReciprocalTree := .branch r226 r241
private def r193 : MobiusReciprocalTree := .branch r194 r225
private def r129 : MobiusReciprocalTree := .branch r130 r193
private def r1 : MobiusReciprocalTree := .branch r2 r129
private abbrev r263 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 0
private theorem rc263 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270336 r263 = true := by decide +kernel

private abbrev r264 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 1
private theorem rc264 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270400 r264 = true := by decide +kernel

private def r262 : MobiusReciprocalTree := .branch r263 r264
private abbrev r266 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 2
private theorem rc266 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270464 r266 = true := by decide +kernel

private abbrev r267 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 3
private theorem rc267 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270528 r267 = true := by decide +kernel

private def r265 : MobiusReciprocalTree := .branch r266 r267
private def r261 : MobiusReciprocalTree := .branch r262 r265
private abbrev r270 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 4
private theorem rc270 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270592 r270 = true := by decide +kernel

private abbrev r271 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 5
private theorem rc271 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270656 r271 = true := by decide +kernel

private def r269 : MobiusReciprocalTree := .branch r270 r271
private abbrev r273 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 6
private theorem rc273 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270720 r273 = true := by decide +kernel

private abbrev r274 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 7
private theorem rc274 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270784 r274 = true := by decide +kernel

private def r272 : MobiusReciprocalTree := .branch r273 r274
private def r268 : MobiusReciprocalTree := .branch r269 r272
private def r260 : MobiusReciprocalTree := .branch r261 r268
private abbrev r278 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 8
private theorem rc278 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270848 r278 = true := by decide +kernel

private abbrev r279 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 9
private theorem rc279 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270912 r279 = true := by decide +kernel

private def r277 : MobiusReciprocalTree := .branch r278 r279
private abbrev r281 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 10
private theorem rc281 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270976 r281 = true := by decide +kernel

private abbrev r282 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 11
private theorem rc282 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271040 r282 = true := by decide +kernel

private def r280 : MobiusReciprocalTree := .branch r281 r282
private def r276 : MobiusReciprocalTree := .branch r277 r280
private abbrev r285 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 12
private theorem rc285 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271104 r285 = true := by decide +kernel

private abbrev r286 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 13
private theorem rc286 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271168 r286 = true := by decide +kernel

private def r284 : MobiusReciprocalTree := .branch r285 r286
private abbrev r288 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 14
private theorem rc288 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271232 r288 = true := by decide +kernel

private abbrev r289 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 15
private theorem rc289 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271296 r289 = true := by decide +kernel

private def r287 : MobiusReciprocalTree := .branch r288 r289
private def r283 : MobiusReciprocalTree := .branch r284 r287
private def r275 : MobiusReciprocalTree := .branch r276 r283
private def r259 : MobiusReciprocalTree := .branch r260 r275
private abbrev r294 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 16
private theorem rc294 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271360 r294 = true := by decide +kernel

private abbrev r295 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 17
private theorem rc295 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271424 r295 = true := by decide +kernel

private def r293 : MobiusReciprocalTree := .branch r294 r295
private abbrev r297 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 18
private theorem rc297 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271488 r297 = true := by decide +kernel

private abbrev r298 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 19
private theorem rc298 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271552 r298 = true := by decide +kernel

private def r296 : MobiusReciprocalTree := .branch r297 r298
private def r292 : MobiusReciprocalTree := .branch r293 r296
private abbrev r301 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 20
private theorem rc301 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271616 r301 = true := by decide +kernel

private abbrev r302 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 21
private theorem rc302 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271680 r302 = true := by decide +kernel

private def r300 : MobiusReciprocalTree := .branch r301 r302
private abbrev r304 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 22
private theorem rc304 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271744 r304 = true := by decide +kernel

private abbrev r305 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 23
private theorem rc305 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271808 r305 = true := by decide +kernel

private def r303 : MobiusReciprocalTree := .branch r304 r305
private def r299 : MobiusReciprocalTree := .branch r300 r303
private def r291 : MobiusReciprocalTree := .branch r292 r299
private abbrev r309 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 24
private theorem rc309 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271872 r309 = true := by decide +kernel

private abbrev r310 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 25
private theorem rc310 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271936 r310 = true := by decide +kernel

private def r308 : MobiusReciprocalTree := .branch r309 r310
private abbrev r312 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 26
private theorem rc312 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272000 r312 = true := by decide +kernel

private abbrev r313 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 27
private theorem rc313 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272064 r313 = true := by decide +kernel

private def r311 : MobiusReciprocalTree := .branch r312 r313
private def r307 : MobiusReciprocalTree := .branch r308 r311
private abbrev r316 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 28
private theorem rc316 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272128 r316 = true := by decide +kernel

private abbrev r317 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 29
private theorem rc317 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272192 r317 = true := by decide +kernel

private def r315 : MobiusReciprocalTree := .branch r316 r317
private abbrev r319 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 30
private theorem rc319 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272256 r319 = true := by decide +kernel

private abbrev r320 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 31
private theorem rc320 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272320 r320 = true := by decide +kernel

private def r318 : MobiusReciprocalTree := .branch r319 r320
private def r314 : MobiusReciprocalTree := .branch r315 r318
private def r306 : MobiusReciprocalTree := .branch r307 r314
private def r290 : MobiusReciprocalTree := .branch r291 r306
private def r258 : MobiusReciprocalTree := .branch r259 r290
private abbrev r326 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 32
private theorem rc326 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272384 r326 = true := by decide +kernel

private abbrev r327 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 33
private theorem rc327 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272448 r327 = true := by decide +kernel

private def r325 : MobiusReciprocalTree := .branch r326 r327
private abbrev r329 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 34
private theorem rc329 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272512 r329 = true := by decide +kernel

private abbrev r330 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 35
private theorem rc330 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272576 r330 = true := by decide +kernel

private def r328 : MobiusReciprocalTree := .branch r329 r330
private def r324 : MobiusReciprocalTree := .branch r325 r328
private abbrev r333 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 36
private theorem rc333 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272640 r333 = true := by decide +kernel

private abbrev r334 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 37
private theorem rc334 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272704 r334 = true := by decide +kernel

private def r332 : MobiusReciprocalTree := .branch r333 r334
private abbrev r336 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 38
private theorem rc336 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272768 r336 = true := by decide +kernel

private abbrev r337 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 39
private theorem rc337 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272832 r337 = true := by decide +kernel

private def r335 : MobiusReciprocalTree := .branch r336 r337
private def r331 : MobiusReciprocalTree := .branch r332 r335
private def r323 : MobiusReciprocalTree := .branch r324 r331
private abbrev r341 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 40
private theorem rc341 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272896 r341 = true := by decide +kernel

private abbrev r342 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 41
private theorem rc342 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272960 r342 = true := by decide +kernel

private def r340 : MobiusReciprocalTree := .branch r341 r342
private abbrev r344 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 42
private theorem rc344 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273024 r344 = true := by decide +kernel

private abbrev r345 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 43
private theorem rc345 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273088 r345 = true := by decide +kernel

private def r343 : MobiusReciprocalTree := .branch r344 r345
private def r339 : MobiusReciprocalTree := .branch r340 r343
private abbrev r348 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 44
private theorem rc348 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273152 r348 = true := by decide +kernel

private abbrev r349 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 45
private theorem rc349 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273216 r349 = true := by decide +kernel

private def r347 : MobiusReciprocalTree := .branch r348 r349
private abbrev r351 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 46
private theorem rc351 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273280 r351 = true := by decide +kernel

private abbrev r352 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 47
private theorem rc352 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273344 r352 = true := by decide +kernel

private def r350 : MobiusReciprocalTree := .branch r351 r352
private def r346 : MobiusReciprocalTree := .branch r347 r350
private def r338 : MobiusReciprocalTree := .branch r339 r346
private def r322 : MobiusReciprocalTree := .branch r323 r338
private abbrev r357 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 48
private theorem rc357 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273408 r357 = true := by decide +kernel

private abbrev r358 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 49
private theorem rc358 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273472 r358 = true := by decide +kernel

private def r356 : MobiusReciprocalTree := .branch r357 r358
private abbrev r360 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 50
private theorem rc360 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273536 r360 = true := by decide +kernel

private abbrev r361 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 51
private theorem rc361 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273600 r361 = true := by decide +kernel

private def r359 : MobiusReciprocalTree := .branch r360 r361
private def r355 : MobiusReciprocalTree := .branch r356 r359
private abbrev r364 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 52
private theorem rc364 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273664 r364 = true := by decide +kernel

private abbrev r365 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 53
private theorem rc365 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273728 r365 = true := by decide +kernel

private def r363 : MobiusReciprocalTree := .branch r364 r365
private abbrev r367 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 54
private theorem rc367 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273792 r367 = true := by decide +kernel

private abbrev r368 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 55
private theorem rc368 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273856 r368 = true := by decide +kernel

private def r366 : MobiusReciprocalTree := .branch r367 r368
private def r362 : MobiusReciprocalTree := .branch r363 r366
private def r354 : MobiusReciprocalTree := .branch r355 r362
private abbrev r372 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 56
private theorem rc372 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273920 r372 = true := by decide +kernel

private abbrev r373 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 57
private theorem rc373 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273984 r373 = true := by decide +kernel

private def r371 : MobiusReciprocalTree := .branch r372 r373
private abbrev r375 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 58
private theorem rc375 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274048 r375 = true := by decide +kernel

private abbrev r376 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 59
private theorem rc376 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274112 r376 = true := by decide +kernel

private def r374 : MobiusReciprocalTree := .branch r375 r376
private def r370 : MobiusReciprocalTree := .branch r371 r374
private abbrev r379 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 60
private theorem rc379 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274176 r379 = true := by decide +kernel

private abbrev r380 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 61
private theorem rc380 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274240 r380 = true := by decide +kernel

private def r378 : MobiusReciprocalTree := .branch r379 r380
private abbrev r382 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 62
private theorem rc382 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274304 r382 = true := by decide +kernel

private abbrev r383 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 63
private theorem rc383 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274368 r383 = true := by decide +kernel

private def r381 : MobiusReciprocalTree := .branch r382 r383
private def r377 : MobiusReciprocalTree := .branch r378 r381
private def r369 : MobiusReciprocalTree := .branch r370 r377
private def r353 : MobiusReciprocalTree := .branch r354 r369
private def r321 : MobiusReciprocalTree := .branch r322 r353
private def r257 : MobiusReciprocalTree := .branch r258 r321
private abbrev r390 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 64
private theorem rc390 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274432 r390 = true := by decide +kernel

private abbrev r391 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 65
private theorem rc391 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274496 r391 = true := by decide +kernel

private def r389 : MobiusReciprocalTree := .branch r390 r391
private abbrev r393 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 66
private theorem rc393 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274560 r393 = true := by decide +kernel

private abbrev r394 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 67
private theorem rc394 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274624 r394 = true := by decide +kernel

private def r392 : MobiusReciprocalTree := .branch r393 r394
private def r388 : MobiusReciprocalTree := .branch r389 r392
private abbrev r397 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 68
private theorem rc397 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274688 r397 = true := by decide +kernel

private abbrev r398 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 69
private theorem rc398 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274752 r398 = true := by decide +kernel

private def r396 : MobiusReciprocalTree := .branch r397 r398
private abbrev r400 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 70
private theorem rc400 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274816 r400 = true := by decide +kernel

private abbrev r401 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 71
private theorem rc401 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274880 r401 = true := by decide +kernel

private def r399 : MobiusReciprocalTree := .branch r400 r401
private def r395 : MobiusReciprocalTree := .branch r396 r399
private def r387 : MobiusReciprocalTree := .branch r388 r395
private abbrev r405 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 72
private theorem rc405 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274944 r405 = true := by decide +kernel

private abbrev r406 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 73
private theorem rc406 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275008 r406 = true := by decide +kernel

private def r404 : MobiusReciprocalTree := .branch r405 r406
private abbrev r408 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 74
private theorem rc408 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275072 r408 = true := by decide +kernel

private abbrev r409 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 75
private theorem rc409 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275136 r409 = true := by decide +kernel

private def r407 : MobiusReciprocalTree := .branch r408 r409
private def r403 : MobiusReciprocalTree := .branch r404 r407
private abbrev r412 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 76
private theorem rc412 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275200 r412 = true := by decide +kernel

private abbrev r413 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 77
private theorem rc413 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275264 r413 = true := by decide +kernel

private def r411 : MobiusReciprocalTree := .branch r412 r413
private abbrev r415 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 78
private theorem rc415 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275328 r415 = true := by decide +kernel

private abbrev r416 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 79
private theorem rc416 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275392 r416 = true := by decide +kernel

private def r414 : MobiusReciprocalTree := .branch r415 r416
private def r410 : MobiusReciprocalTree := .branch r411 r414
private def r402 : MobiusReciprocalTree := .branch r403 r410
private def r386 : MobiusReciprocalTree := .branch r387 r402
private abbrev r421 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 80
private theorem rc421 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275456 r421 = true := by decide +kernel

private abbrev r422 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 81
private theorem rc422 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275520 r422 = true := by decide +kernel

private def r420 : MobiusReciprocalTree := .branch r421 r422
private abbrev r424 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 82
private theorem rc424 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275584 r424 = true := by decide +kernel

private abbrev r425 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 83
private theorem rc425 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275648 r425 = true := by decide +kernel

private def r423 : MobiusReciprocalTree := .branch r424 r425
private def r419 : MobiusReciprocalTree := .branch r420 r423
private abbrev r428 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 84
private theorem rc428 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275712 r428 = true := by decide +kernel

private abbrev r429 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 85
private theorem rc429 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275776 r429 = true := by decide +kernel

private def r427 : MobiusReciprocalTree := .branch r428 r429
private abbrev r431 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 86
private theorem rc431 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275840 r431 = true := by decide +kernel

private abbrev r432 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 87
private theorem rc432 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275904 r432 = true := by decide +kernel

private def r430 : MobiusReciprocalTree := .branch r431 r432
private def r426 : MobiusReciprocalTree := .branch r427 r430
private def r418 : MobiusReciprocalTree := .branch r419 r426
private abbrev r436 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 88
private theorem rc436 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275968 r436 = true := by decide +kernel

private abbrev r437 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 89
private theorem rc437 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276032 r437 = true := by decide +kernel

private def r435 : MobiusReciprocalTree := .branch r436 r437
private abbrev r439 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 90
private theorem rc439 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276096 r439 = true := by decide +kernel

private abbrev r440 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 91
private theorem rc440 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276160 r440 = true := by decide +kernel

private def r438 : MobiusReciprocalTree := .branch r439 r440
private def r434 : MobiusReciprocalTree := .branch r435 r438
private abbrev r443 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 92
private theorem rc443 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276224 r443 = true := by decide +kernel

private abbrev r444 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 93
private theorem rc444 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276288 r444 = true := by decide +kernel

private def r442 : MobiusReciprocalTree := .branch r443 r444
private abbrev r446 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 94
private theorem rc446 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276352 r446 = true := by decide +kernel

private abbrev r447 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 95
private theorem rc447 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276416 r447 = true := by decide +kernel

private def r445 : MobiusReciprocalTree := .branch r446 r447
private def r441 : MobiusReciprocalTree := .branch r442 r445
private def r433 : MobiusReciprocalTree := .branch r434 r441
private def r417 : MobiusReciprocalTree := .branch r418 r433
private def r385 : MobiusReciprocalTree := .branch r386 r417
private abbrev r453 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 96
private theorem rc453 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276480 r453 = true := by decide +kernel

private abbrev r454 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 97
private theorem rc454 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276544 r454 = true := by decide +kernel

private def r452 : MobiusReciprocalTree := .branch r453 r454
private abbrev r456 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 98
private theorem rc456 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276608 r456 = true := by decide +kernel

private abbrev r457 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 99
private theorem rc457 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276672 r457 = true := by decide +kernel

private def r455 : MobiusReciprocalTree := .branch r456 r457
private def r451 : MobiusReciprocalTree := .branch r452 r455
private abbrev r460 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 100
private theorem rc460 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276736 r460 = true := by decide +kernel

private abbrev r461 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 101
private theorem rc461 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276800 r461 = true := by decide +kernel

private def r459 : MobiusReciprocalTree := .branch r460 r461
private abbrev r463 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 102
private theorem rc463 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276864 r463 = true := by decide +kernel

private abbrev r464 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 103
private theorem rc464 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276928 r464 = true := by decide +kernel

private def r462 : MobiusReciprocalTree := .branch r463 r464
private def r458 : MobiusReciprocalTree := .branch r459 r462
private def r450 : MobiusReciprocalTree := .branch r451 r458
private abbrev r468 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 104
private theorem rc468 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276992 r468 = true := by decide +kernel

private abbrev r469 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 105
private theorem rc469 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277056 r469 = true := by decide +kernel

private def r467 : MobiusReciprocalTree := .branch r468 r469
private abbrev r471 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 106
private theorem rc471 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277120 r471 = true := by decide +kernel

private abbrev r472 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 107
private theorem rc472 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277184 r472 = true := by decide +kernel

private def r470 : MobiusReciprocalTree := .branch r471 r472
private def r466 : MobiusReciprocalTree := .branch r467 r470
private abbrev r475 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 108
private theorem rc475 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277248 r475 = true := by decide +kernel

private abbrev r476 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 109
private theorem rc476 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277312 r476 = true := by decide +kernel

private def r474 : MobiusReciprocalTree := .branch r475 r476
private abbrev r478 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 110
private theorem rc478 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277376 r478 = true := by decide +kernel

private abbrev r479 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 111
private theorem rc479 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277440 r479 = true := by decide +kernel

private def r477 : MobiusReciprocalTree := .branch r478 r479
private def r473 : MobiusReciprocalTree := .branch r474 r477
private def r465 : MobiusReciprocalTree := .branch r466 r473
private def r449 : MobiusReciprocalTree := .branch r450 r465
private abbrev r484 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 112
private theorem rc484 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277504 r484 = true := by decide +kernel

private abbrev r485 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 113
private theorem rc485 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277568 r485 = true := by decide +kernel

private def r483 : MobiusReciprocalTree := .branch r484 r485
private abbrev r487 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 114
private theorem rc487 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277632 r487 = true := by decide +kernel

private abbrev r488 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 115
private theorem rc488 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277696 r488 = true := by decide +kernel

private def r486 : MobiusReciprocalTree := .branch r487 r488
private def r482 : MobiusReciprocalTree := .branch r483 r486
private abbrev r491 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 116
private theorem rc491 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277760 r491 = true := by decide +kernel

private abbrev r492 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 117
private theorem rc492 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277824 r492 = true := by decide +kernel

private def r490 : MobiusReciprocalTree := .branch r491 r492
private abbrev r494 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 118
private theorem rc494 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277888 r494 = true := by decide +kernel

private abbrev r495 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 119
private theorem rc495 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277952 r495 = true := by decide +kernel

private def r493 : MobiusReciprocalTree := .branch r494 r495
private def r489 : MobiusReciprocalTree := .branch r490 r493
private def r481 : MobiusReciprocalTree := .branch r482 r489
private abbrev r499 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 120
private theorem rc499 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278016 r499 = true := by decide +kernel

private abbrev r500 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 121
private theorem rc500 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278080 r500 = true := by decide +kernel

private def r498 : MobiusReciprocalTree := .branch r499 r500
private abbrev r502 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 122
private theorem rc502 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278144 r502 = true := by decide +kernel

private abbrev r503 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 123
private theorem rc503 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278208 r503 = true := by decide +kernel

private def r501 : MobiusReciprocalTree := .branch r502 r503
private def r497 : MobiusReciprocalTree := .branch r498 r501
private abbrev r506 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 124
private theorem rc506 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278272 r506 = true := by decide +kernel

private abbrev r507 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 125
private theorem rc507 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278336 r507 = true := by decide +kernel

private def r505 : MobiusReciprocalTree := .branch r506 r507
private abbrev r509 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 126
private theorem rc509 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278400 r509 = true := by decide +kernel

private abbrev r510 : MobiusReciprocalTree := publishedReciprocalLeaf 7 mobiusReciprocal1200001Block033 127
private theorem rc510 : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278464 r510 = true := by decide +kernel

private def r508 : MobiusReciprocalTree := .branch r509 r510
private def r504 : MobiusReciprocalTree := .branch r505 r508
private def r496 : MobiusReciprocalTree := .branch r497 r504
private def r480 : MobiusReciprocalTree := .branch r481 r496
private def r448 : MobiusReciprocalTree := .branch r449 r480
private def r384 : MobiusReciprocalTree := .branch r385 r448
private def r256 : MobiusReciprocalTree := .branch r257 r384
private def r0 : MobiusReciprocalTree := .branch r1 r256

theorem mobiusReciprocalSqrtPair016_checked_complete : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 262144 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block032 mobiusReciprocal1200001Block033) = true :=
  (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 8 262144 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 7 262144 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 6 262144 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 262144 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 262144 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 262144 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 262144 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262144 _ _ (by decide) rc8 rc9 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262272 _ _ (by decide) rc11 rc12 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 262400 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262400 _ _ (by decide) rc15 rc16 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262528 _ _ (by decide) rc18 rc19 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 262656 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 262656 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262656 _ _ (by decide) rc23 rc24 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262784 _ _ (by decide) rc26 rc27 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 262912 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 262912 _ _ (by decide) rc30 rc31 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263040 _ _ (by decide) rc33 rc34 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 263168 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 263168 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 263168 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263168 _ _ (by decide) rc39 rc40 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263296 _ _ (by decide) rc42 rc43 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 263424 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263424 _ _ (by decide) rc46 rc47 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263552 _ _ (by decide) rc49 rc50 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 263680 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 263680 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263680 _ _ (by decide) rc54 rc55 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263808 _ _ (by decide) rc57 rc58 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 263936 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 263936 _ _ (by decide) rc61 rc62 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264064 _ _ (by decide) rc64 rc65 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 264192 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 264192 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 264192 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 264192 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264192 _ _ (by decide) rc71 rc72 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264320 _ _ (by decide) rc74 rc75 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 264448 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264448 _ _ (by decide) rc78 rc79 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264576 _ _ (by decide) rc81 rc82 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 264704 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 264704 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264704 _ _ (by decide) rc86 rc87 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264832 _ _ (by decide) rc89 rc90 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 264960 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 264960 _ _ (by decide) rc93 rc94 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265088 _ _ (by decide) rc96 rc97 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 265216 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 265216 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 265216 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265216 _ _ (by decide) rc102 rc103 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265344 _ _ (by decide) rc105 rc106 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 265472 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265472 _ _ (by decide) rc109 rc110 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265600 _ _ (by decide) rc112 rc113 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 265728 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 265728 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265728 _ _ (by decide) rc117 rc118 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265856 _ _ (by decide) rc120 rc121 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 265984 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 265984 _ _ (by decide) rc124 rc125 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266112 _ _ (by decide) rc127 rc128 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 6 266240 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 266240 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 266240 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 266240 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 266240 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266240 _ _ (by decide) rc135 rc136 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266368 _ _ (by decide) rc138 rc139 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 266496 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266496 _ _ (by decide) rc142 rc143 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266624 _ _ (by decide) rc145 rc146 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 266752 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 266752 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266752 _ _ (by decide) rc150 rc151 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 266880 _ _ (by decide) rc153 rc154 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 267008 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267008 _ _ (by decide) rc157 rc158 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267136 _ _ (by decide) rc160 rc161 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 267264 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 267264 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 267264 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267264 _ _ (by decide) rc166 rc167 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267392 _ _ (by decide) rc169 rc170 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 267520 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267520 _ _ (by decide) rc173 rc174 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267648 _ _ (by decide) rc176 rc177 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 267776 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 267776 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267776 _ _ (by decide) rc181 rc182 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 267904 _ _ (by decide) rc184 rc185 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 268032 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268032 _ _ (by decide) rc188 rc189 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268160 _ _ (by decide) rc191 rc192 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 268288 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 268288 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 268288 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 268288 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268288 _ _ (by decide) rc198 rc199 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268416 _ _ (by decide) rc201 rc202 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 268544 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268544 _ _ (by decide) rc205 rc206 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268672 _ _ (by decide) rc208 rc209 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 268800 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 268800 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268800 _ _ (by decide) rc213 rc214 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 268928 _ _ (by decide) rc216 rc217 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 269056 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269056 _ _ (by decide) rc220 rc221 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269184 _ _ (by decide) rc223 rc224 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 269312 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 269312 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 269312 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269312 _ _ (by decide) rc229 rc230 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269440 _ _ (by decide) rc232 rc233 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 269568 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269568 _ _ (by decide) rc236 rc237 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269696 _ _ (by decide) rc239 rc240 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 269824 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 269824 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269824 _ _ (by decide) rc244 rc245 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 269952 _ _ (by decide) rc247 rc248 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 270080 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270080 _ _ (by decide) rc251 rc252 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270208 _ _ (by decide) rc254 rc255 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 7 270336 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 6 270336 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 270336 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 270336 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 270336 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 270336 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270336 _ _ (by decide) rc263 rc264 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270464 _ _ (by decide) rc266 rc267 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 270592 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270592 _ _ (by decide) rc270 rc271 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270720 _ _ (by decide) rc273 rc274 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 270848 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 270848 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270848 _ _ (by decide) rc278 rc279 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 270976 _ _ (by decide) rc281 rc282 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 271104 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271104 _ _ (by decide) rc285 rc286 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271232 _ _ (by decide) rc288 rc289 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 271360 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 271360 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 271360 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271360 _ _ (by decide) rc294 rc295 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271488 _ _ (by decide) rc297 rc298 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 271616 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271616 _ _ (by decide) rc301 rc302 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271744 _ _ (by decide) rc304 rc305 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 271872 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 271872 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 271872 _ _ (by decide) rc309 rc310 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272000 _ _ (by decide) rc312 rc313 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 272128 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272128 _ _ (by decide) rc316 rc317 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272256 _ _ (by decide) rc319 rc320 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 272384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 272384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 272384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 272384 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272384 _ _ (by decide) rc326 rc327 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272512 _ _ (by decide) rc329 rc330 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 272640 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272640 _ _ (by decide) rc333 rc334 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272768 _ _ (by decide) rc336 rc337 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 272896 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 272896 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 272896 _ _ (by decide) rc341 rc342 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273024 _ _ (by decide) rc344 rc345 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 273152 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273152 _ _ (by decide) rc348 rc349 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273280 _ _ (by decide) rc351 rc352 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 273408 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 273408 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 273408 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273408 _ _ (by decide) rc357 rc358 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273536 _ _ (by decide) rc360 rc361 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 273664 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273664 _ _ (by decide) rc364 rc365 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273792 _ _ (by decide) rc367 rc368 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 273920 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 273920 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 273920 _ _ (by decide) rc372 rc373 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274048 _ _ (by decide) rc375 rc376 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 274176 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274176 _ _ (by decide) rc379 rc380 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274304 _ _ (by decide) rc382 rc383 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 6 274432 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 274432 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 274432 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 274432 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 274432 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274432 _ _ (by decide) rc390 rc391 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274560 _ _ (by decide) rc393 rc394 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 274688 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274688 _ _ (by decide) rc397 rc398 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274816 _ _ (by decide) rc400 rc401 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 274944 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 274944 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 274944 _ _ (by decide) rc405 rc406 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275072 _ _ (by decide) rc408 rc409 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 275200 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275200 _ _ (by decide) rc412 rc413 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275328 _ _ (by decide) rc415 rc416 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 275456 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 275456 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 275456 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275456 _ _ (by decide) rc421 rc422 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275584 _ _ (by decide) rc424 rc425 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 275712 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275712 _ _ (by decide) rc428 rc429 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275840 _ _ (by decide) rc431 rc432 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 275968 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 275968 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 275968 _ _ (by decide) rc436 rc437 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276096 _ _ (by decide) rc439 rc440 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 276224 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276224 _ _ (by decide) rc443 rc444 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276352 _ _ (by decide) rc446 rc447 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 5 276480 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 276480 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 276480 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 276480 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276480 _ _ (by decide) rc453 rc454 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276608 _ _ (by decide) rc456 rc457 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 276736 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276736 _ _ (by decide) rc460 rc461 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276864 _ _ (by decide) rc463 rc464 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 276992 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 276992 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 276992 _ _ (by decide) rc468 rc469 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277120 _ _ (by decide) rc471 rc472 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 277248 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277248 _ _ (by decide) rc475 rc476 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277376 _ _ (by decide) rc478 rc479 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 4 277504 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 277504 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 277504 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277504 _ _ (by decide) rc484 rc485 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277632 _ _ (by decide) rc487 rc488 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 277760 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277760 _ _ (by decide) rc491 rc492 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 277888 _ _ (by decide) rc494 rc495 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 3 278016 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 278016 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278016 _ _ (by decide) rc499 rc500 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278144 _ _ (by decide) rc502 rc503 (by decide +kernel)) (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 2 278272 _ _ (by decide) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278272 _ _ (by decide) rc506 rc507 (by decide +kernel)) (mobiusReciprocalSqrtTreeCheck_join (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 1 278400 _ _ (by decide) rc509 rc510 (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel)) (by decide +kernel))

end Helfgott
end

open Helfgott
theorem solution : mobiusReciprocalSqrtTreeCheck (mobiusTreeValue 16 mobiusTable1200001) 1000000000000 1200001 9 262144 (MobiusReciprocalTree.branch mobiusReciprocal1200001Block032 mobiusReciprocal1200001Block033) = true := Helfgott.mobiusReciprocalSqrtPair016_checked_complete
#print axioms solution
