-- Prove2me | solution 1 for MazurProof.N13FormalCurveOverlap.ofOverlap_mul
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:16:05.91599+00:00
-- url     : https://prove2.me/submissions/8143ca59-2555-40f3-a0f1-fd34b5261365

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
/-- The defining quadratic relation of the actual formal curve. -/
theorem vClass_relation :
    vClass ^ 2 +
        algebraMap Laurent FormalCurve
          (N13FormalLineBundleCech.hInfinity (R := R₂)) *
          vClass =
      algebraMap Laurent FormalCurve
        (N13FormalLineBundleCech.rhsInfinity (R := R₂)) := by
  have h := AdjoinRoot.eval₂_root formalCurvePoly
  rw [formalCurvePoly] at h
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_mul] at h
  exact sub_eq_zero.mp h
/-- Pair multiplication is exactly multiplication in the actual quadratic
formal-curve algebra. -/
theorem ofOverlap_mul
    (z w : Overlap) :
    ofOverlap (N13FormalLineBundleCech.mulOverlap z w) =
      ofOverlap z * ofOverlap w := by
  have hv :
      vClass ^ 2 =
        algebraMap Laurent FormalCurve
            (N13FormalLineBundleCech.rhsInfinity (R := R₂)) -
          algebraMap Laurent FormalCurve
              (N13FormalLineBundleCech.hInfinity (R := R₂)) *
            vClass := by
    linear_combination vClass_relation
  change
    algebraMap Laurent FormalCurve
          (z.1 * w.1 +
            z.2 * w.2 *
              N13FormalLineBundleCech.rhsInfinity (R := R₂)) +
        algebraMap Laurent FormalCurve
            (z.1 * w.2 + z.2 * w.1 -
              z.2 * w.2 *
                N13FormalLineBundleCech.hInfinity (R := R₂)) *
          vClass =
      (algebraMap Laurent FormalCurve z.1 +
          algebraMap Laurent FormalCurve z.2 * vClass) *
        (algebraMap Laurent FormalCurve w.1 +
          algebraMap Laurent FormalCurve w.2 * vClass)
  simp only [map_add, map_sub, map_mul]
  linear_combination
    -(algebraMap Laurent FormalCurve z.2 *
      algebraMap Laurent FormalCurve w.2) * hv
/-! ## Restriction of the actual affine coordinate ring -/
end
end MazurProof.N13FormalCurveOverlap
end

end

theorem solution : type_of% @MazurProof.N13FormalCurveOverlap.ofOverlap_mul := @MazurProof.N13FormalCurveOverlap.ofOverlap_mul
