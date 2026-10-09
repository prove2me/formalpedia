-- Prove2me | solution 1 for MazurProof.N13FormalCurveOverlap.formalCurvePoly_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T04:27:42.36598+00:00
-- url     : https://prove2.me/submissions/ace3b462-2f03-47e7-b81f-d0eeacede154

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13FormalCurveOverlap =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalCurveOverlap =====
section
/-!
# The actual formal overlap algebra for the N13 integral curve

The pair multiplication used by the formal Čech calculation is not an
abstract two-dimensional algebra.  It is the normal-form multiplication in
the quadratic algebra

`R₂((t))[v] / (v² + (1+t²+t³)v - (t+t²))`.

This file identifies the two descriptions and constructs the restriction
homomorphism from the actual affine coordinate ring by

`x ↦ t⁻¹`, `y ↦ t⁻³v`.

Thus a unit obtained from a genuine local trivialization gives, without any
extra inverse hypothesis, the `NearIdentityTransition` consumed by the
Čech--Nakayama theorem.
-/
open Polynomial
namespace MazurProof.N13FormalCurveOverlap
noncomputable section
open HahnSeries
open scoped LaurentSeries
attribute [local instance] MazurProof.N13FormalCurveOverlap.instFactPrimeOfNatNat_fLT
theorem formalCurvePoly_natDegree :
    formalCurvePoly.natDegree = 2 := by
  unfold formalCurvePoly
  compute_degree <;> norm_num
/-! ## Restriction of the actual affine coordinate ring -/
end
end MazurProof.N13FormalCurveOverlap
end

end

theorem solution : type_of% @MazurProof.N13FormalCurveOverlap.formalCurvePoly_natDegree := @MazurProof.N13FormalCurveOverlap.formalCurvePoly_natDegree
