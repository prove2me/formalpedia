-- Prove2me | solution 1 for MazurTransfer.order49_point_map_addOrderOf_orderSevenPointMap_of_order_fortyNine
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T03:31:25.367559+00:00
-- url     : https://prove2.me/submissions/6bda821d-5b93-41c1-b68a-0ef9cad43e72

import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyPointConstructors
import Mathlib
import Theorems.Thm_MazurTransfer_order49_point_map_orderSevenPointMap_kernel_killed_by_seven
open Polynomial
theorem MazurTransfer.Order49ImageOrderConsumer.MazurTorsion.Kubert.orderSevenPointMap_kernel_killed_by_seven {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {P : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hP : MazurTorsion.Kubert.orderSevenPointMap d P = 0) :
    (7 : ℕ) • P = 0 := by
  apply MazurTransfer.order49_point_map_orderSevenPointMap_kernel_killed_by_seven <;> assumption
namespace MazurTransfer.Order49ImageOrderConsumer
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/




open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert


























































































































/-- The exact-order consequence needed at the first stage of the order-`49`
tower.  Full additivity of the explicit point function is unnecessary here:
it suffices to know compatibility with the single multiple `7 • Q`. -/
theorem addOrderOf_orderSevenPointMap_of_order_fortyNine
    {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0)
    (hmap : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q) :
    addOrderOf (MazurTorsion.Kubert.orderSevenPointMap d Q) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  apply addOrderOf_eq_prime
  · rw [← hmap]
    exact hkernel
  · intro hzero
    have hkilled : (7 : ℕ) • Q = 0 :=
      MazurTransfer.Order49ImageOrderConsumer.MazurTorsion.Kubert.orderSevenPointMap_kernel_killed_by_seven hzero
    have hdvd : (49 : ℕ) ∣ 7 := by
      rw [← hQ]
      exact addOrderOf_dvd_of_nsmul_eq_zero hkilled
    norm_num at hdvd









end MazurTorsion.Kubert

end MazurTransfer.Order49ImageOrderConsumer

theorem solution {d : ℚ} [(MazurTorsion.Kubert.orderSevenFamily d).IsElliptic]
    {Q : (MazurTorsion.Kubert.orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) = 0)
    (hmap : MazurTorsion.Kubert.orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • MazurTorsion.Kubert.orderSevenPointMap d Q) :
    addOrderOf (MazurTorsion.Kubert.orderSevenPointMap d Q) = 7 := by
  apply MazurTransfer.Order49ImageOrderConsumer.MazurTorsion.Kubert.addOrderOf_orderSevenPointMap_of_order_fortyNine <;> assumption
#print axioms solution
