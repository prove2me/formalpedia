-- Prove2me | solution 1 for MazurProof.N13IntegralFractionalHull.functionField_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:40:07.671718+00:00
-- url     : https://prove2.me/submissions/7adaaeea-db3a-4560-9132-9c97e31b07bb

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

-- ===== FLT.Assumptions.MazurProof.N13IntegralFractionalHull =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13IntegralFractionalHull =====
section
/-!
# Divisorial hulls on the N13 integral model

The N13 generic affine ring is the vertical localization of its integral
good-model ring.  This file proves that the common function field is also the
fraction field of the integral model and that vertical extension commutes with
inverse fractional ideals.

The reverse inclusion is the substantive point: a fractional ideal over the
Noetherian integral model has finitely many generators, so one vertical scalar
clears all denominators of their products with a generic inverse section.
Consequently the divisorial double inverse of a contracted invertible generic
ideal has exactly the original generic fibre.  No affine generator or
principality assumption is used.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13IntegralFractionalHull
noncomputable section
attribute [local instance] MazurProof.N13IntegralFractionalHull.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralRationalAlgebra
attribute [local instance] MazurProof.N13IntegralFractionalHull.integralRingDomain
attribute [local instance] MazurProof.N13IntegralFractionalHull.rationalRingLocalization
/-- The function field of the generic fibre is also the fraction field of
the integral model. -/
theorem functionField_isFractionRing :
    IsFractionRing IntegralRing FunctionField := by
  let M := N13IntegralModelContraction.verticalScalars
  let N := nonZeroDivisors RationalRing
  have hloc :
      IsLocalization
          (N.comap (algebraMap IntegralRing RationalRing))
          FunctionField :=
    IsLocalization.localization_localization_isLocalization_of_has_all_units
      M N FunctionField (fun x hx => by
        change x ∈ nonZeroDivisors RationalRing
        rw [mem_nonZeroDivisors_iff_ne_zero]
        exact hx.ne_zero)
  have hsub :
      N.comap (algebraMap IntegralRing RationalRing) =
        nonZeroDivisors IntegralRing := by
    ext a
    change
      integralToRational a ∈ nonZeroDivisors RationalRing ↔
        a ∈ nonZeroDivisors IntegralRing
    simp only [mem_nonZeroDivisors_iff_ne_zero]
    simpa only [map_zero] using
      (integralToRational_injective.ne_iff
        (x := a) (y := 0))
  rw [hsub] at hloc
  exact hloc
end
end MazurProof.N13IntegralFractionalHull
end

end

theorem solution : type_of% @MazurProof.N13IntegralFractionalHull.functionField_isFractionRing := @MazurProof.N13IntegralFractionalHull.functionField_isFractionRing
