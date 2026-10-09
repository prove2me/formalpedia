-- Prove2me | solution 1 for MazurProof.N13GaussianCubicField.minpoly_alpha
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:18:35.516923+00:00
-- url     : https://prove2.me/submissions/bb30739e-eb23-40c0-90dd-9f13ce02828c

import Mathlib
import Definitions.Def_MazurN13_L3

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GaussianCubicField =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianCubicField =====
section
/-!
# The global N13 Gaussian cubic field

We form the fraction field `K = Frac(ℤ[i])` and adjoin a root of the
translated Gaussian cubic.  Its Eisenstein property proves irreducibility,
while the discriminant--Eisenstein criterion identifies the monogenic
Gaussian order with the full relative integral closure.

This file contains no class-group computation and no integral-basis search.
-/
open Algebra Module Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GaussianCubicField
noncomputable section
open N13GaussianGlobalArithmetic
attribute [local instance] MazurProof.N13GaussianCubicField.instFactIrreduciblePolynomialKHK
attribute [local instance] MazurProof.N13GaussianCubicField.fieldL
attribute [local instance] MazurProof.N13GaussianCubicField.finiteKL
attribute [local instance] MazurProof.N13GaussianCubicField.separableKL
/-- The integral minimal polynomial is exactly the translated cubic. -/
theorem minpoly_alpha :
    minpoly GI alpha = h := by
  apply Polynomial.map_injective
    (f := algebraMap GI K)
    (FaithfulSMul.algebraMap_injective GI K)
  calc
    (minpoly GI alpha).map (algebraMap GI K) =
        minpoly K alpha :=
      (minpoly.isIntegrallyClosed_eq_field_fractions'
        K alpha_integral).symm
    _ = hK := by
      change minpoly K (AdjoinRoot.root hK) = hK
      exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hK_monic
    _ = h.map (algebraMap GI K) := rfl
/-! ## The relative integral basis -/
attribute [local instance] MazurProof.N13GaussianCubicField.faithfulGIL
/-! ## Discriminant of the relative integral basis -/
attribute [local instance] MazurProof.N13GaussianCubicField.integralClosureLocalization
end
end MazurProof.N13GaussianCubicField
end

end

theorem solution : type_of% @MazurProof.N13GaussianCubicField.minpoly_alpha := @MazurProof.N13GaussianCubicField.minpoly_alpha
