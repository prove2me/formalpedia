-- Prove2me | solution 1 for MazurProof.N13SpecialCuspReduction.cuspOfCoordinate_cuspCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:30:43.906048+00:00
-- url     : https://prove2.me/submissions/b953f4c7-a1bc-460c-bfe4-0877d7e74562

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
theorem cuspOfCoordinate_cuspCoordinate
    (c : Cusp13) :
    cuspOfCoordinate (cuspCoordinate c) = c := by
  cases c <;> simp [cuspCoordinate, cuspOfCoordinate]
end
end MazurProof.N13SpecialCuspReduction
end

end

theorem solution : type_of% @MazurProof.N13SpecialCuspReduction.cuspOfCoordinate_cuspCoordinate := @MazurProof.N13SpecialCuspReduction.cuspOfCoordinate_cuspCoordinate
