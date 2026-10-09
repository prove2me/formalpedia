-- Prove2me | solution 1 for MazurProof.N13FiniteAffineTwoChart.integralPointIdeal_quotient_finite
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:05:58.427541+00:00
-- url     : https://prove2.me/submissions/9fef66b4-6d2c-4076-81fe-bf03f63b17b1

import Mathlib
import Definitions.Def_MazurN13_L4

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13FiniteAffineTwoChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FiniteAffineTwoChart =====
section
/-!
# Proper two-chart closure of a finite N13 affine divisor

An invertible ideal on the affine chart need not by itself record its
behaviour at infinity.  For an ideal with finite support over the two-adic
coefficient ring, however, the affine coordinate is integral in the
quotient.  A monic equation for that coordinate reflects to an equation with
constant coefficient one on the infinity chart.  Hence the infinity
uniformizer is a unit modulo the contracted overlap ideal.

The principal-localization patching theorem then upgrades invertibility on
the punctured infinity chart to invertibility on the full infinity chart.
This supplies proper extensions for finite N13 graph ideals, including
integral affine points and the finite irreducible quadratic branch, without
choosing reciprocal coordinates.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13FiniteAffineTwoChart
noncomputable section
attribute [local instance] MazurProof.N13FiniteAffineTwoChart.instFactPrimeOfNatNat_fLT
/-! ## Integral affine point lines -/
/-- The quotient by the monic graph ideal of an integral affine point is
finite over the two-adic coefficient ring. -/
theorem integralPointIdeal_quotient_finite
    (P : N13IntegralAffinePointSpread.IntegralPoint) :
    Module.Finite R₂
      (AffineCurve ⧸
        N13IntegralAffinePointSpread.pointIdeal P) := by
  let D :=
    N13IntegralAffinePointSpread.integralSemiGraph P
  letI : Module.Finite R₂
      (N13GeneralizedMumfordIntegral.MumfordResidue D) :=
    D.u_monic.finite_quotient
  exact
    Module.Finite.equiv
      (N13GeneralizedMumfordIntegral.mumfordQuotientAlgEquiv
        D).symm.toLinearEquiv
/-! ## Finite quadratic lines -/
end
end MazurProof.N13FiniteAffineTwoChart
end

end

theorem solution : type_of% @MazurProof.N13FiniteAffineTwoChart.integralPointIdeal_quotient_finite := @MazurProof.N13FiniteAffineTwoChart.integralPointIdeal_quotient_finite
