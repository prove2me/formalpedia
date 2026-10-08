-- Prove2me | solution 1 for MazurTransfer.order49_point_map_orderSevenPointMap_some_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:26:48.732338+00:00
-- url     : https://prove2.me/submissions/82bcccf1-afa7-41ba-9fb6-d0c72c7def86

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
open Polynomial
namespace MazurTransfer.Order49PointMapHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert




































































































/-- Evaluation of the total point map away from the kernel poles. -/
theorem orderSevenPointMap_some_of_not_kernelX
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) =
      MazurTorsion.Kubert.orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h))) := by
  simp [MazurTorsion.Kubert.orderSevenPointMap, hx]

/-- An affine point maps to infinity exactly at one of the three kernel
abscissae. -/
theorem orderSevenPointMap_some_eq_zero_iff
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) = 0 ↔
      MazurTorsion.Kubert.OrderSevenKernelX d x := by
  by_cases hx : MazurTorsion.Kubert.OrderSevenKernelX d x
  · simp [MazurTorsion.Kubert.orderSevenPointMap, hx]
  · rw [MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX hP hx]
    exact ⟨fun h ↦ (WeierstrassCurve.Affine.Point.some_ne_zero _ h).elim,
      fun h ↦ (hx h).elim⟩





























end MazurTorsion.Kubert

end MazurTransfer.Order49PointMapHelpers

theorem solution {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) = 0 ↔
      MazurTorsion.Kubert.OrderSevenKernelX d x := by
  apply MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_eq_zero_iff <;> assumption
#print axioms solution
