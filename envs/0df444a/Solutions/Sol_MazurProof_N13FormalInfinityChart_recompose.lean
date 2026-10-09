-- Prove2me | solution 1 for MazurProof.N13FormalInfinityChart.recompose
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:09:05.250016+00:00
-- url     : https://prove2.me/submissions/e2b71403-d8c3-40c5-ba20-5eff5035d696

import Mathlib
import Definitions.Def_MazurN13_L3
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_recompose
import Theorems.Thm_MazurProof_SexticMumford_recompose

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
/-!
# Integral generalized Mumford graph quotients for N13

For the good equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`,

evaluation on a graph `Y=v mod u` identifies the graph quotient with
`R[X]/(u)` over any nontrivial commutative base ring.  If the base is a
domain and `u` is monic, this quotient is free and hence torsion-free.
Consequently every graph ideal is saturated with respect to each nonzero
base scalar.

This is the elementary integral algebra needed before reduction modulo two;
it uses neither normality of the affine ring nor a Picard scheme.
-/
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
theorem normalPoly_eq_C_add_C_mul_X
    [Nontrivial R]
    (z : CoordinateRing (R := R)) :
    normalPoly z = C (coeff0 z) + C (coeffY z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly =
        C ((g %ₘ curvePoly).coeff 0) +
          C ((g %ₘ curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly) curvePoly_monic
        (n := 2) (by rw [curvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
namespace TwoAdic
end TwoAdic
end
end MazurProof.N13GeneralizedMumfordIntegral
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodCoordinateRingTwo =====
section
/-!
# The affine coordinate ring of the N13 good fibre at two

The good characteristic-two equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`

defines a quadratic extension of `F₂(X)`.  This file constructs its affine
coordinate ring as an `AdjoinRoot` and proves irreducibility structurally.
The proof uses degree dominance and two coefficient comparisons; it does not
enumerate polynomials over `F₂`.
-/
open Polynomial
open FractionalIdeal (coeIdeal_mul)
open scoped nonZeroDivisors
namespace MazurProof.N13GoodCoordinateRingTwo
noncomputable section
theorem curvePoly_degree : curvePoly.degree = 2 := by
  rw [degree_eq_natDegree curvePoly_monic.ne_zero,
    curvePoly_natDegree]
  norm_num
theorem normalPoly_eq_C_add_C_mul_X (z : CoordinateRing) :
    normalPoly z = C (coeff0 z) + C (coeffY z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly =
        C ((g %ₘ curvePoly).coeff 0) +
          C ((g %ₘ curvePoly).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly) curvePoly_monic
        (n := 2) (by rw [curvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
/-! ## Generalized Mumford graph ideals -/
/-! ## Evaluation at a generalized Mumford graph -/
end
end MazurProof.N13GoodCoordinateRingTwo
end

end

-- ===== FLT.Assumptions.MazurProof.SexticMumfordBasis =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordBasis =====
section
/-!
# The rank-two basis of a smooth sextic affine ring

For a model `Y² = f(X)`, every element of the affine coordinate ring is
written uniquely as `p(X) + q(X)Y`.  This is the coefficient API used by
the Mumford ideal and normal-form layers.
-/
open Polynomial
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K)
theorem normalPoly_eq_C_add_C_mul_X (z : CoordinateRing M) :
    normalPoly M z = C (coeff0 M z) + C (coeffY M z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly M =
        C ((g %ₘ curvePoly M).coeff 0) +
          C ((g %ₘ curvePoly M).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly M) (curvePoly_monic M)
        (n := 2) (by rw [degree_curvePoly]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
/-! ## Hyperelliptic conjugation and the quadratic norm -/
end
end MazurProof.SexticMumford
end

end

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
theorem normalPoly_eq_C_add_C_mul_X
    (z : FormalCurve) :
    normalPoly z =
      C (coeff0 z) + C (coeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change
        g %ₘ formalCurvePoly =
          C ((g %ₘ formalCurvePoly).coeff 0) +
            C ((g %ₘ formalCurvePoly).coeff 1) * X
      have hsum :=
        Polynomial.sum_modByMonic_coeff
          (p := g) (q := formalCurvePoly)
          formalCurvePoly_monic (n := 2)
          (by rw [formalCurvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
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
theorem infinityCurvePoly_natDegree :
    infinityCurvePoly.natDegree = 2 := by
  unfold infinityCurvePoly
  compute_degree <;> norm_num
theorem infinityCurvePoly_degree :
    infinityCurvePoly.degree = 2 := by
  rw [degree_eq_natDegree infinityCurvePoly_monic.ne_zero,
    infinityCurvePoly_natDegree]
  norm_num
/-! ## Normal form on the complete chart -/
theorem normalPoly_eq_C_add_C_mul_X
    (z : InfinityCurve) :
    normalPoly z =
      C (coeff0 z) + C (coeffV z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change
        g %ₘ infinityCurvePoly =
          C ((g %ₘ infinityCurvePoly).coeff 0) +
            C ((g %ₘ infinityCurvePoly).coeff 1) * X
      have hsum :=
        Polynomial.sum_modByMonic_coeff
          (p := g) (q := infinityCurvePoly)
          infinityCurvePoly_monic (n := 2)
          (by rw [infinityCurvePoly_degree]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm
/-- Every complete-chart function has a unique pair of power-series
coefficients in the basis `1,v`. -/
theorem recompose
    (z : InfinityCurve) :
    algebraMap Power InfinityCurve (coeff0 z) +
        algebraMap Power InfinityCurve (coeffV z) * vClass =
      z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        algebraMap Power InfinityCurve
              (coeff0 (AdjoinRoot.mk infinityCurvePoly g)) +
            algebraMap Power InfinityCurve
                (coeffV (AdjoinRoot.mk infinityCurvePoly g)) *
              vClass =
            AdjoinRoot.mk infinityCurvePoly
              (C (coeff0 (AdjoinRoot.mk infinityCurvePoly g)) +
                C (coeffV (AdjoinRoot.mk infinityCurvePoly g)) * X) := by
                  simp [vClass, AdjoinRoot.algebraMap_eq]
        _ =
            AdjoinRoot.mk infinityCurvePoly
              (normalPoly (AdjoinRoot.mk infinityCurvePoly g)) := by
                  rw [normalPoly_eq_C_add_C_mul_X]
        _ = AdjoinRoot.mk infinityCurvePoly g :=
          AdjoinRoot.mk_leftInverse infinityCurvePoly_monic _
end
end MazurProof.N13FormalInfinityChart
end

end

theorem solution : type_of% @MazurProof.N13FormalInfinityChart.recompose := @MazurProof.N13FormalInfinityChart.recompose
