-- Prove2me | solution 1 for MazurProof.N13FormalCurveOverlap.ofOverlap_toOverlap
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:23:38.772259+00:00
-- url     : https://prove2.me/submissions/369bd0c7-f9af-452e-bc55-d8f022aa3382

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_curvePoly_natDegree
import Theorems.Thm_MazurProof_N13GoodCoordinateRingTwo_curvePoly_natDegree

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
/-- Reconstruction from the pair of normal-form coefficients. -/
theorem ofOverlap_toOverlap
    (z : FormalCurve) :
    ofOverlap (toOverlap z) = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        ofOverlap (toOverlap (AdjoinRoot.mk formalCurvePoly g)) =
            AdjoinRoot.mk formalCurvePoly
              (C (coeff0 (AdjoinRoot.mk formalCurvePoly g)) +
                C (coeffV (AdjoinRoot.mk formalCurvePoly g)) * X) := by
                  simp [ofOverlap, toOverlap, vClass,
                    AdjoinRoot.algebraMap_eq]
        _ =
            AdjoinRoot.mk formalCurvePoly
              (normalPoly (AdjoinRoot.mk formalCurvePoly g)) := by
                  rw [normalPoly_eq_C_add_C_mul_X]
        _ = AdjoinRoot.mk formalCurvePoly g :=
          AdjoinRoot.mk_leftInverse formalCurvePoly_monic _
/-! ## Restriction of the actual affine coordinate ring -/
end
end MazurProof.N13FormalCurveOverlap
end

end

theorem solution : type_of% @MazurProof.N13FormalCurveOverlap.ofOverlap_toOverlap := @MazurProof.N13FormalCurveOverlap.ofOverlap_toOverlap
