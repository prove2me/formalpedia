-- Prove2me | solution 1 for MazurTransfer.order49_point_map_not_orderSevenKernelX_of_order_fortyNine
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:01:29.961424+00:00
-- url     : https://prove2.me/submissions/f96ec574-992b-44f2-bcff-530a62255bda

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_kernel_killed_by_seven
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_some_eq_zero_iff
open Polynomial
theorem MazurTransfer.Order49PointNonvanishingHelpers.MazurTorsion.Kubert.orderSevenPointMap_kernel_killed_by_seven {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hP : MazurTorsion.Kubert.orderSevenPointMap d P = 0) :
    (7 : ℕ) • P = 0 := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_kernel_killed_by_seven <;> assumption

theorem MazurTransfer.Order49PointNonvanishingHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_eq_zero_iff {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y) :
    MazurTorsion.Kubert.orderSevenPointMap d (.some x y hP) = 0 ↔
      MazurTorsion.Kubert.OrderSevenKernelX d x := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_some_eq_zero_iff <;> assumption
namespace MazurTransfer.Order49PointNonvanishingHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert
























































































































/-- An affine point of exact order `49` cannot lie in the marked
order-seven kernel. -/
theorem not_orderSevenKernelX_of_order_fortyNine
    {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49) :
    ¬MazurTorsion.Kubert.OrderSevenKernelX d x := by
  intro hx
  have hzero : MazurTorsion.Kubert.orderSevenPointMap d
      (WeierstrassCurve.Affine.Point.some x y hP) = 0 :=
    (MazurTransfer.Order49PointNonvanishingHelpers.MazurTorsion.Kubert.orderSevenPointMap_some_eq_zero_iff hP).2 hx
  have hkilled := MazurTransfer.Order49PointNonvanishingHelpers.MazurTorsion.Kubert.orderSevenPointMap_kernel_killed_by_seven hzero
  have hdvd : (49 : ℕ) ∣ 7 := by
    rw [← horder]
    exact addOrderOf_dvd_of_nsmul_eq_zero hkilled
  norm_num at hdvd











end MazurTorsion.Kubert

end MazurTransfer.Order49PointNonvanishingHelpers

theorem solution {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49) :
    ¬MazurTorsion.Kubert.OrderSevenKernelX d x := by
  apply MazurTransfer.Order49PointNonvanishingHelpers.MazurTorsion.Kubert.not_orderSevenKernelX_of_order_fortyNine <;> assumption
#print axioms solution
