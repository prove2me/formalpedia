-- Prove2me | solution 1 for MazurProof.N13FormalCurveOverlap.affineCurve_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:06:08.284056+00:00
-- url     : https://prove2.me/submissions/d0851132-395d-4b8c-850e-7101d725a721

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
/-! ## Restriction of the actual affine coordinate ring -/
@[simp] theorem polyAtTInv_X :
    polyAtTInv X = tPow (-1) := by
  simp [polyAtTInv]
/-- The affine coefficient `x³+x+1` becomes
`t⁻³(1+t²+t³)`. -/
theorem polyAtTInv_hPoly :
    polyAtTInv
        (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
      tPow (-3) *
        N13FormalLineBundleCech.hInfinity (R := R₂) := by
  simp only [N13GeneralizedMumfordIntegral.hPoly,
    map_add, map_pow, map_one, polyAtTInv_X]
  change
    tPow (-1) ^ 3 + tPow (-1) + 1 =
      tPow (-3) *
        (tPow 0 + tPow 2 + tPow 3)
  simp only [pow_succ, tPow_mul, mul_add, mul_one,
    tPow_zero]
  norm_num
/-- The affine right-hand side `x⁵+x⁴` becomes
`t⁻⁶(t+t²)`. -/
theorem polyAtTInv_rhsPoly :
    polyAtTInv
        (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
      tPow (-6) *
        N13FormalLineBundleCech.rhsInfinity (R := R₂) := by
  simp only [N13GeneralizedMumfordIntegral.rhsPoly,
    map_add, map_pow, polyAtTInv_X]
  change
    tPow (-1) ^ 5 + tPow (-1) ^ 4 =
      tPow (-6) * (tPow 1 + tPow 2)
  simp only [pow_succ, tPow_mul, mul_add]
  norm_num
/-- The proposed image of `y` satisfies the actual affine equation after
the substitution `x=t⁻¹`. -/
theorem affineCurve_relation :
    (N13GeneralizedMumfordIntegral.curvePoly (R := R₂)).eval₂
        affineCoeffMap yImage =
      0 := by
  simp only [N13GeneralizedMumfordIntegral.curvePoly,
    Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_mul]
  rw [show affineCoeffMap
          (N13GeneralizedMumfordIntegral.hPoly (R := R₂)) =
        algebraMap Laurent FormalCurve
          (tPow (-3) *
            N13FormalLineBundleCech.hInfinity (R := R₂)) by
      simp [affineCoeffMap, polyAtTInv_hPoly]]
  rw [show affineCoeffMap
          (N13GeneralizedMumfordIntegral.rhsPoly (R := R₂)) =
        algebraMap Laurent FormalCurve
          (tPow (-6) *
            N13FormalLineBundleCech.rhsInfinity (R := R₂)) by
      simp [affineCoeffMap, polyAtTInv_rhsPoly]]
  simp only [yImage, map_mul]
  have ht :
      algebraMap Laurent FormalCurve (tPow (-3)) ^ 2 =
        algebraMap Laurent FormalCurve (tPow (-6)) := by
    rw [← map_pow]
    congr 1
    simp [pow_two, tPow_mul]
  rw [show
      (algebraMap Laurent FormalCurve (tPow (-3)) * vClass) ^ 2 =
        algebraMap Laurent FormalCurve (tPow (-6)) *
          vClass ^ 2 by
      rw [mul_pow, ht]]
  rw [← ht]
  linear_combination
    algebraMap Laurent FormalCurve (tPow (-3)) ^ 2 *
      (sub_eq_zero.mpr vClass_relation)
end
end MazurProof.N13FormalCurveOverlap
end

end

theorem solution : type_of% @MazurProof.N13FormalCurveOverlap.affineCurve_relation := @MazurProof.N13FormalCurveOverlap.affineCurve_relation
