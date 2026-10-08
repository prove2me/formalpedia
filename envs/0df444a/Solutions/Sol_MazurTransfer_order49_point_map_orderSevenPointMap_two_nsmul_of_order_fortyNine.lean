-- Prove2me | solution 1 for MazurTransfer.order49_point_map_orderSevenPointMap_two_nsmul_of_order_fortyNine
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:15:08.344692+00:00
-- url     : https://prove2.me/submissions/5b817e8f-26bc-4751-9337-81be48b34485

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
import Theorems.Thm_MazurTransfer_order49_coordinate_orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates
import Theorems.Thm_MazurTransfer_order49_coordinate_orderSevenVelu_double_coordinates
open Polynomial
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero
theorem MazurTransfer.Order49PointMapDoublingConsumer.MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hcoordinates : ∀ {x y : ℚ}
      (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y),
      addOrderOf
          (WeierstrassCurve.Affine.Point.some x y hP :
            (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49 →
        MazurTorsion.Kubert.OrderSevenDoublingCoordinates d x y)
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • Q) =
      (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
  apply MazurTransfer.order49_coordinate_orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates <;> assumption

theorem MazurTransfer.Order49PointMapDoublingConsumer.MazurTorsion.Kubert.orderSevenVelu_double_coordinates {d x y : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    (hP : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point) = 49) :
    MazurTorsion.Kubert.OrderSevenDoublingCoordinates d x y := by
  apply MazurTransfer.order49_coordinate_orderSevenVelu_double_coordinates <;> assumption
namespace MazurTransfer.Order49PointMapDoublingConsumer
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert























































/-- On an exact-order-`49` point, the explicit total order-seven Vélu map
commutes with tangent doubling. -/
theorem orderSevenPointMap_two_nsmul_of_order_fortyNine
    {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • Q) =
      (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
  apply MazurTransfer.Order49PointMapDoublingConsumer.MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates
    (fun hP horder ↦ MazurTransfer.Order49PointMapDoublingConsumer.MazurTorsion.Kubert.orderSevenVelu_double_coordinates hP horder)
  exact hQ











end MazurTorsion.Kubert

end MazurTransfer.Order49PointMapDoublingConsumer

theorem solution {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • Q) =
      (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
  apply MazurTransfer.Order49PointMapDoublingConsumer.MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine <;> assumption
#print axioms solution
