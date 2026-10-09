-- Prove2me | solution 1 for MazurProof.N13GlobalKummerIdealSquare.exists_scaledIntegralMumford
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:50:41.670986+00:00
-- url     : https://prove2.me/submissions/cd77308b-b833-4563-b6fb-cb1ca9ee057c

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

-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerNormalization =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerNormalization =====
section
/-!
# Global primitive normalization of N13 Kummer values

A rational Mumford polynomial need not have integral coefficients.  We clear
all denominators simultaneously over `ℤ`, remove the polynomial content, and
evaluate the resulting primitive polynomial at the integral Gaussian-cubic
generator `α + 9`.

The resulting element lies in the actual absolute ring of integers and
differs from the original Kummer value by one nonzero rational scalar.
Primitivity and the degree bound are retained, and the norm of the integral
representative remains a rational square.  Thus denominator clearing is
separated cleanly from the subsequent ideal factorization.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerNormalization
noncomputable section
open N13GaussianFieldEquiv
attribute [local instance] MazurProof.N13GlobalKummerNormalization.fieldL
attribute [local instance] MazurProof.N13GlobalKummerNormalization.intNormalizationMonoid
attribute [local instance] MazurProof.N13GlobalKummerNormalization.intNormalizedGCDMonoid
theorem integralNormalization_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    integralNormalization p ≠ 0 := by
  exact
    (IsFractionRing.integerNormalization_eq_zero_iff
      (A := ℤ) (K := ℚ)).not.mpr hp
theorem integralNormalization_content_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    (integralNormalization p).content ≠ 0 := by
  exact
    Polynomial.content_eq_zero_iff.not.mpr
      (integralNormalization_ne_zero hp)
theorem primitiveNormalization_spec
    {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧
      (primitiveNormalization p).map
          (algebraMap ℤ ℚ) =
        C c * p := by
  let U₀ : ℤ[X] := integralNormalization p
  let U : ℤ[X] := primitiveNormalization p
  obtain ⟨b, hb, hclear⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors ℤ) p
  have hb0 : b ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbc :
      algebraMap ℤ ℚ b ≠ 0 :=
    (IsFractionRing.injective ℤ ℚ).ne hb0
  have hcontent :
      algebraMap ℤ ℚ U₀.content ≠ 0 :=
    (IsFractionRing.injective ℤ ℚ).ne
      (integralNormalization_content_ne_zero hp)
  let c : ℚ :=
    (algebraMap ℤ ℚ U₀.content)⁻¹ *
      algebraMap ℤ ℚ b
  refine
    ⟨c, mul_ne_zero (inv_ne_zero hcontent) hbc, ?_⟩
  have hdecomp :
      U₀.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ U₀.content) *
          U.map (algebraMap ℤ ℚ) := by
    simpa only [U₀, U, integralNormalization,
      primitiveNormalization, Polynomial.map_mul,
      Polynomial.map_C] using
      congrArg (Polynomial.map (algebraMap ℤ ℚ))
        U₀.eq_C_content_mul_primPart
  have hcleared :
      U₀.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ b) * p := by
    simpa only [U₀, integralNormalization,
      Algebra.smul_def, Polynomial.algebraMap_apply] using
      hclear
  calc
    U.map (algebraMap ℤ ℚ) =
        1 * U.map (algebraMap ℤ ℚ) := by rw [one_mul]
    _ =
        (C (algebraMap ℤ ℚ U₀.content)⁻¹ *
            C (algebraMap ℤ ℚ U₀.content)) *
          U.map (algebraMap ℤ ℚ) := by
      rw [← C_mul, inv_mul_cancel₀ hcontent,
        C_1, one_mul]
    _ =
        C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          (C (algebraMap ℤ ℚ U₀.content) *
            U.map (algebraMap ℤ ℚ)) := by ring
    _ =
        C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          (C (algebraMap ℤ ℚ b) * p) := by
      rw [← hdecomp, hcleared]
    _ =
        (C (algebraMap ℤ ℚ U₀.content)⁻¹ *
          C (algebraMap ℤ ℚ b)) * p := by ring
    _ = C c * p := by rw [← C_mul]
end
end MazurProof.N13GlobalKummerNormalization
end

end

-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerIdealSquare =====
section
/-!
# The good-locus square ideal of a normalized N13 Kummer value

Primitive normalization removes the arbitrary content of a rational
Mumford polynomial, but it does not make the other polynomial in the
Mumford pair integral.  We clear those remaining denominators
*homogeneously*: if

`f - v² = u w`

and `U = c u` is the primitive integral normalization, then a single
nonzero integer `d` can be chosen together with integral `V,W` so that

`d² f - V² = U W`.

After evaluating at the integral branch point and inverting the derivative
of `d² f`, the branch ideal `(U(θ),V(θ))` squares to `(U(θ))`.  This is the
principal ideal of the previously constructed `normalizedKummerInteger`.
Thus every denominator and bad-reduction prime is isolated in one
canonical localization; no prime factorization or valuation enumeration is
used.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerIdealSquare
noncomputable section
open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
attribute [local instance] MazurProof.N13GlobalKummerIdealSquare.fieldL
/-- Every rational polynomial has a nonzero integral scalar multiple with
integral coefficients. -/
theorem exists_integral_scalar_multiple (p : ℚ[X]) :
    ∃ b : ℤ, b ≠ 0 ∧ ∃ P : ℤ[X],
      P.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ b) * p := by
  obtain ⟨b, hb, hP⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors ℤ) p
  exact
    ⟨b, mem_nonZeroDivisors_iff_ne_zero.mp hb,
      IsLocalization.integerNormalization
        (nonZeroDivisors ℤ) p, by
          simpa only [Algebra.smul_def,
            Polynomial.algebraMap_apply] using hP⟩
/-- Simultaneous denominator clearing preserves the Mumford equation in
homogeneous form. -/
theorem exists_scaledIntegralMumford
    (D : N13LowDegreeKummerHom.LowRep) :
    Nonempty (ScaledIntegralMumford D) := by
  obtain ⟨w, hw⟩ := D.toSemi.curve_dvd
  change
    N13Mumford.f ℚ - D.toSemi.v ^ 2 =
      D.toSemi.u * w at hw
  obtain ⟨c, hc, hU⟩ :=
    primitiveNormalization_spec D.toSemi.u_monic.ne_zero
  obtain ⟨bV, hbV, V₀, hV₀⟩ :=
    exists_integral_scalar_multiple D.toSemi.v
  obtain ⟨bW, hbW, W₀, hW₀⟩ :=
    exists_integral_scalar_multiple (C c⁻¹ * w)
  let d : ℤ := bV * bW
  let V : ℤ[X] := C bW * V₀
  let W : ℤ[X] := (C bV) ^ 2 * C bW * W₀
  have hd : d ≠ 0 :=
    mul_ne_zero hbV hbW
  have hV :
      V.map (algebraMap ℤ ℚ) =
        C (algebraMap ℤ ℚ d) * D.toSemi.v := by
    simp only [V, d, Polynomial.map_mul, Polynomial.map_C,
      hV₀, map_mul]
    ring
  have hW :
      W.map (algebraMap ℤ ℚ) =
        C ((algebraMap ℤ ℚ d) ^ 2 * c⁻¹) * w := by
    simp only [W, d, Polynomial.map_mul, Polynomial.map_C,
      hW₀, map_mul, map_pow]
    rw [Polynomial.map_pow, Polynomial.map_C]
    ring
  refine ⟨⟨d, hd, V, W, ?_⟩⟩
  apply Polynomial.map_injective
    (f := algebraMap ℤ ℚ)
    (IsFractionRing.injective ℤ ℚ)
  simp only [Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, hV, hW, hU,
    map_pow]
  rw [N13SexticIrreducible.fInt_map_rat]
  have hcInv : c * c⁻¹ = 1 :=
    mul_inv_cancel₀ hc
  have hscalar :
      C c * C ((algebraMap ℤ ℚ d) ^ 2 * c⁻¹) =
        C (algebraMap ℤ ℚ d) ^ 2 := by
    rw [← C_mul, ← C_pow]
    congr 1
    calc
      c * ((algebraMap ℤ ℚ d) ^ 2 * c⁻¹) =
          (c * c⁻¹) * (algebraMap ℤ ℚ d) ^ 2 := by ring
      _ = _ := by rw [hcInv, one_mul]
  rw [show
    C (algebraMap ℤ ℚ d) ^ 2 *
          N13Mumford.f ℚ -
        (C (algebraMap ℤ ℚ d) * D.toSemi.v) ^ 2 =
      C (algebraMap ℤ ℚ d) ^ 2 *
        (N13Mumford.f ℚ - D.toSemi.v ^ 2) by ring,
    hw]
  rw [← hscalar]
  ring
/-! ## The principal-ideal endpoint -/
end
end MazurProof.N13GlobalKummerIdealSquare
end

end

theorem solution : type_of% @MazurProof.N13GlobalKummerIdealSquare.exists_scaledIntegralMumford := @MazurProof.N13GlobalKummerIdealSquare.exists_scaledIntegralMumford
