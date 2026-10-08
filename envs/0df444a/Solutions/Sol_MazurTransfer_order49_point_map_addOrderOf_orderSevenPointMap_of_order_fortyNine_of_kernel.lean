-- Prove2me | solution 1 for MazurTransfer.order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T05:01:24.421184+00:00
-- url     : https://prove2.me/submissions/16e0e9b4-d9f0-4b8d-8c64-d07418204f0e

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49MarkedOriginPoint
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
import Theorems.Thm_MazurTransfer_order49_marked_origin_exists_eq_nsmul_orderSevenOrigin_of_pointMap_eq_zero
import Theorems.Thm_MazurTransfer_order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_two_nsmul_of_order_fortyNine
import Theorems.Thm_MazurTransfer_order49_translation_orderSevenPointMap_add_nsmul_origin_of_order_fortyNine
open Polynomial
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero
theorem MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0)
    (hmap : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q) :
    addOrderOf (MazurTorsion.Kubert.orderSevenPointMap d Q) = 7 := by
  apply MazurTransfer.order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine <;> assumption

theorem MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.exists_eq_nsmul_orderSevenOrigin_of_pointMap_eq_zero {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {R : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hR : MazurTorsion.Kubert.orderSevenPointMap d R = 0) :
    ∃ n : ℕ, n < 7 ∧ R = n • MazurTorsion.Kubert.orderSevenOrigin d := by
  apply MazurTransfer.order49_marked_origin_exists_eq_nsmul_orderSevenOrigin_of_pointMap_eq_zero <;> assumption

theorem MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.orderSevenPointMap_add_nsmul_origin_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) (n : ℕ) :
    MazurTorsion.Kubert.orderSevenPointMap d (Q + n • MazurTorsion.Kubert.orderSevenOrigin d) =
      MazurTorsion.Kubert.orderSevenPointMap d Q := by
  apply MazurTransfer.order49_translation_orderSevenPointMap_add_nsmul_origin_of_order_fortyNine <;> assumption

theorem MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • Q) =
      (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_two_nsmul_of_order_fortyNine <;> assumption
namespace MazurTransfer.Order49SevenMultipleImageOrderConsumers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

























































/-- If `7 • Q` lies in the explicit zero fiber, doubling compatibility and
translation invariance force the Vélu map to commute with that multiple. -/
theorem orderSevenPointMap_seven_nsmul_of_order_fortyNine
    {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
  have h2Q : addOrderOf ((2 : ℕ) • Q) = 49 := by
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  have h4Q : addOrderOf ((4 : ℕ) • Q) = 49 := by
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  have hdoubleQ :=
    MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine hQ
  have hdouble2Q := MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine
    (Q := (2 : ℕ) • Q) h2Q
  have hdouble4Q := MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.orderSevenPointMap_two_nsmul_of_order_fortyNine
    (Q := (4 : ℕ) • Q) h4Q
  have hmap4 : MazurTorsion.Kubert.orderSevenPointMap d ((4 : ℕ) • Q) =
      (4 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
    calc
      MazurTorsion.Kubert.orderSevenPointMap d ((4 : ℕ) • Q) =
          MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • ((2 : ℕ) • Q)) := by
            rw [← mul_nsmul]
      _ = (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • Q) :=
        hdouble2Q
      _ = (2 : ℕ) • ((2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q) := by
        rw [hdoubleQ]
      _ = (4 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
        rw [← mul_nsmul]
  have hmap8 : MazurTorsion.Kubert.orderSevenPointMap d ((8 : ℕ) • Q) =
      (8 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
    calc
      MazurTorsion.Kubert.orderSevenPointMap d ((8 : ℕ) • Q) =
          MazurTorsion.Kubert.orderSevenPointMap d ((2 : ℕ) • ((4 : ℕ) • Q)) := by
            rw [← mul_nsmul]
      _ = (2 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d ((4 : ℕ) • Q) :=
        hdouble4Q
      _ = (2 : ℕ) • ((4 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q) := by
        rw [hmap4]
      _ = (8 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q := by
        rw [← mul_nsmul]
  obtain ⟨n, _hn, h7Q⟩ :=
    MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.exists_eq_nsmul_orderSevenOrigin_of_pointMap_eq_zero hkernel
  have hinvariant : MazurTorsion.Kubert.orderSevenPointMap d ((8 : ℕ) • Q) =
      MazurTorsion.Kubert.orderSevenPointMap d Q := by
    calc
      MazurTorsion.Kubert.orderSevenPointMap d ((8 : ℕ) • Q) =
          MazurTorsion.Kubert.orderSevenPointMap d (Q + (7 : ℕ) • Q) := by
            congr 2
            abel
      _ = MazurTorsion.Kubert.orderSevenPointMap d (Q + n • MazurTorsion.Kubert.orderSevenOrigin d) := by
        rw [h7Q]
      _ = MazurTorsion.Kubert.orderSevenPointMap d Q :=
        MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.orderSevenPointMap_add_nsmul_origin_of_order_fortyNine hQ n
  have h8image : (8 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q =
      MazurTorsion.Kubert.orderSevenPointMap d Q := hmap8.symm.trans hinvariant
  have h7image : (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q = 0 := by
    calc
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q =
          (8 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q -
            MazurTorsion.Kubert.orderSevenPointMap d Q := by abel
      _ = 0 := by rw [h8image]; simp
  rw [hkernel]
  exact h7image.symm

/-- Under the single zero-fiber hypothesis at `7 • Q`, the Vélu image of
an exact-order-`49` point has exact order seven. -/
theorem addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel
    {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    addOrderOf (MazurTorsion.Kubert.orderSevenPointMap d Q) = 7 := by
  exact MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine hQ hkernel
    (MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.orderSevenPointMap_seven_nsmul_of_order_fortyNine hQ hkernel)







end MazurTorsion.Kubert

end MazurTransfer.Order49SevenMultipleImageOrderConsumers

theorem solution {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    addOrderOf (MazurTorsion.Kubert.orderSevenPointMap d Q) = 7 := by
  apply MazurTransfer.Order49SevenMultipleImageOrderConsumers.MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel <;> assumption
#print axioms solution
