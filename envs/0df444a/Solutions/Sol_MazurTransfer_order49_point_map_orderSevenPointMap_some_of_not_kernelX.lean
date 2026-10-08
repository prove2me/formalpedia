-- Prove2me | solution 1 for MazurTransfer.order49_point_map_orderSevenPointMap_some_of_not_kernelX
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:26:19.811051+00:00
-- url     : https://prove2.me/submissions/3ed7c55e-2f1b-48f3-9d2d-588ab65ada1f

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































end MazurTorsion.Kubert

end MazurTransfer.Order49PointMapHelpers

theorem solution {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : ¬MazurTorsion.Kubert.OrderSevenKernelX d x) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) =
      MazurTorsion.Kubert.orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h))) := by
  apply MazurTransfer.Order49PointMapHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_of_not_kernelX <;> assumption
#print axioms solution
