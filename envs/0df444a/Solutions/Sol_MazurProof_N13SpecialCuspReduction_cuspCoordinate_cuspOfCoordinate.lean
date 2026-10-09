-- Prove2me | solution 1 for MazurProof.N13SpecialCuspReduction.cuspCoordinate_cuspOfCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:28:44.261485+00:00
-- url     : https://prove2.me/submissions/21597800-1daf-4239-bf09-fecdbfeacaeb

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13SpecialCuspReduction =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialCuspReduction =====
section
/-!
# The six N13 cusps on the special fibre

The good characteristic-two model has three hyperelliptic base points and
two sheets over each of them.  The six rational cusps reduce to these six
points bijectively.  This file records that correspondence as an explicit
equivalence.

The proof uses only the structural fact that every element of `F₂` is zero
or one.  It does not enumerate divisors or Jacobian representatives.
-/
namespace MazurProof.N13SpecialCuspReduction
noncomputable section
open N13AbelFiberTwoModel
theorem cuspCoordinate_cuspOfCoordinate
    (z : BasePoint × K) :
    cuspCoordinate (cuspOfCoordinate z) = z := by
  rcases z with ⟨b, y⟩
  have hy : y = 0 ∨ y = 1 :=
    N13GoodModelTwo.fixedTwo_eq_zero_or_one y (ZMod.pow_card y)
  rcases b with x | u
  · have hx : x = 0 ∨ x = 1 :=
      N13GoodModelTwo.fixedTwo_eq_zero_or_one x (ZMod.pow_card x)
    rcases hx with rfl | rfl <;>
      rcases hy with rfl | rfl <;>
      simp [cuspCoordinate, cuspOfCoordinate]
  · cases u
    rcases hy with rfl | rfl <;>
      simp [cuspCoordinate, cuspOfCoordinate]
end
end MazurProof.N13SpecialCuspReduction
end

end

theorem solution : type_of% @MazurProof.N13SpecialCuspReduction.cuspCoordinate_cuspOfCoordinate := @MazurProof.N13SpecialCuspReduction.cuspCoordinate_cuspOfCoordinate
