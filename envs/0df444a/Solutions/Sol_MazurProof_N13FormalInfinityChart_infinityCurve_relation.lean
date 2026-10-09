-- Prove2me | solution 1 for MazurProof.N13FormalInfinityChart.infinityCurve_relation
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:37:56.518981+00:00
-- url     : https://prove2.me/submissions/c740c4fb-df33-4897-a3d0-ba53f8a695b4

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
end
end MazurProof.N13FormalCurveOverlap
end

end

-- ===== FLT.Assumptions.MazurProof.N13FormalInfinityChart =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13FormalInfinityChart =====
section
/-!
# The actual formal infinity chart of the N13 integral curve

The additive Čech calculation described the infinity-chart image as pairs of
power series.  This file realizes that submodule as the image of the actual
quadratic formal curve

`ℤ₂[[t]][v] / (v² + (1+t²+t³)v - (t+t²))`

inside the punctured formal overlap.  In particular, the previously defined
`infinitySections` is neither an approximation nor a coefficientwise
superset: it is exactly the restriction image of the genuine chart ring.
-/
open Polynomial
namespace MazurProof.N13FormalInfinityChart
noncomputable section
open HahnSeries
open scoped PowerSeries LaurentSeries
attribute [local instance] MazurProof.N13FormalInfinityChart.instFactPrimeOfNatNat_fLT
@[simp] theorem includePowerRing_hPower :
    includePowerRing hPower =
      N13FormalLineBundleCech.hInfinity (R := R₂) := by
  simp [includePowerRing, hPower,
    N13FormalLineBundleCech.hInfinity,
    N13FormalLineBundleCech.tPow]
@[simp] theorem includePowerRing_rhsPower :
    includePowerRing rhsPower =
      N13FormalLineBundleCech.rhsInfinity (R := R₂) := by
  simp [includePowerRing, rhsPower,
    N13FormalLineBundleCech.rhsInfinity,
    N13FormalLineBundleCech.tPow]
/-- The overlap coordinate `v` satisfies the complete-chart equation. -/
theorem infinityCurve_relation :
    infinityCurvePoly.eval₂
        infinityCoeffMap N13FormalCurveOverlap.vClass =
      0 := by
  simp only [infinityCurvePoly, Polynomial.eval₂_sub,
    Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_mul]
  change
    N13FormalCurveOverlap.vClass ^ 2 +
          algebraMap Laurent FormalCurve
              (includePowerRing hPower) *
            N13FormalCurveOverlap.vClass -
        algebraMap Laurent FormalCurve
          (includePowerRing rhsPower) =
      0
  rw [includePowerRing_hPower, includePowerRing_rhsPower]
  exact sub_eq_zero.mpr N13FormalCurveOverlap.vClass_relation
/-! ## Normal form on the complete chart -/
end
end MazurProof.N13FormalInfinityChart
end

end

theorem solution : type_of% @MazurProof.N13FormalInfinityChart.infinityCurve_relation := @MazurProof.N13FormalInfinityChart.infinityCurve_relation
