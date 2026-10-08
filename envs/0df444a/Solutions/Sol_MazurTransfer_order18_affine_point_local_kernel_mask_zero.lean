-- Prove2me | solution 1 for MazurTransfer.order18_affine_point_local_kernel_mask_zero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T18:14:04.479287+00:00
-- url     : https://prove2.me/submissions/d3b687d7-a29f-44ca-9706-443a2d00c9e7

import Mathlib
import Theorems.Thm_MazurTransfer_order18_selected_local_point_image_trivial
import Theorems.Thm_MazurTransfer_order18_selected_local_kernel_representative_separation

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI

Checked bridge between the two original local arithmetic interfaces.
Named downstream consumer: the unchanged unconditional quotient doubling theorem.
-/

theorem solution (x y : MazurTorsion.XOneEighteenMinimalTwoDescentModel.K)
    (h : MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentCurve.toAffine.Nonsingular x y)
    (hv : algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K
      MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x -
        MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentRootInM ≠ 0)
    (mask : Fin 16)
    (hmask : MazurTorsion.XOneEighteenGlobalSelmerBridge.fieldSquareclass
      (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K
        MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x -
          MazurTorsion.XOneEighteenMinimalTwoDescentModel.minimalDescentRootInM) hv =
      MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative mask) : mask = 0 := by
  have hl := MazurTransfer.order18_selected_local_point_image_trivial x y h hv
  rw [hmask] at hl
  exact (MazurTransfer.order18_selected_local_kernel_representative_separation mask).mp hl

#print axioms solution
