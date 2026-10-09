-- Prove2me | solution 1 for MazurProof.N13QuadraticTwoChartSpreadSaturation.mul_scalar_saturated_of_left_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:17:27.393384+00:00
-- url     : https://prove2.me/submissions/346c5c03-8982-4a80-ab23-0f5e40d1636c

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

-- ===== FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpreadSaturation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpreadSaturation =====
section
/-!
# Vertical saturation of split quadratic N13 spreads

The affine ideal of a two-chart line is invertible in the common function
field.  If two such ideals have no vertical scalar torsion, their product has
none either: multiply by the inverse of the first fractional ideal, cancel the
base scalar in the second ideal, and multiply the first ideal back.

Applying this cancellation theorem to the valuation-independent point-line
constructor proves vertical saturation of `pairLine`.  Coincident points are
allowed, so the result covers both split secants and repeated-root tangents.
-/
open scoped nonZeroDivisors
namespace MazurProof.N13QuadraticTwoChartSpreadSaturation
noncomputable section
attribute [local instance] MazurProof.N13QuadraticTwoChartSpreadSaturation.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13QuadraticTwoChartSpreadSaturation.integralRationalAlgebra
attribute [local instance] MazurProof.N13QuadraticTwoChartSpreadSaturation.integralFunctionFieldFractionRing
/-- The product of two vertically saturated integral ideals is vertically
saturated when the first ideal is invertible in the common function field.

The inverse fractional ideal supplies a finite dual-basis-free cancellation:
an element of the first ideal is tested after multiplication by every inverse
section.  Each resulting integral element lies in the second ideal by scalar
saturation, and multiplying the first ideal back recovers product
membership. -/
theorem mul_scalar_saturated_of_left_isUnit
    (I J : Ideal A)
    (hunit : IsUnit (I : Frac))
    (hI :
      ∀ (r : R₂), r ≠ 0 → ∀ a : A,
        algebraMap R₂ A r * a ∈ I → a ∈ I)
    (hJ :
      ∀ (r : R₂), r ≠ 0 → ∀ a : A,
        algebraMap R₂ A r * a ∈ J → a ∈ J) :
    ∀ (r : R₂), r ≠ 0 → ∀ a : A,
      algebraMap R₂ A r * a ∈ I * J → a ∈ I * J := by
  intro r hr a hra
  have haI : a ∈ I :=
    hI r hr a (Ideal.mul_le_left hra)
  let U : Fracˣ := hunit.unit
  have hU : (U : Frac) = (I : Frac) := hunit.unit_spec
  have hUinv_mul : (↑U⁻¹ : Frac) * (I : Frac) = 1 := by
    rw [← hU]
    exact Units.inv_mul U
  have hU_mul_inv : (I : Frac) * (↑U⁻¹ : Frac) = 1 := by
    rw [← hU]
    exact Units.mul_inv U
  have hInvSpan :
      (↑U⁻¹ : Frac) *
          FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) ≤
        (J : Frac) := by
    rw [mul_comm, FractionalIdeal.spanSingleton_mul_le_iff]
    intro z hz
    have haFrac : algebraMap A K a ∈ (I : Frac) :=
      FractionalIdeal.mem_coeIdeal_of_mem A⁰ haI
    have hzaOne : z * algebraMap A K a ∈ (1 : Frac) := by
      rw [← hUinv_mul]
      exact FractionalIdeal.mul_mem_mul hz haFrac
    have hzaTop :
        z * algebraMap A K a ∈ ((⊤ : Ideal A) : Frac) := by
      simpa using hzaOne
    obtain ⟨c, -, hc⟩ :=
      (FractionalIdeal.mem_coeIdeal A⁰).mp hzaTop
    have hraFrac :
        algebraMap A K (algebraMap R₂ A r * a) ∈
          (I : Frac) * (J : Frac) := by
      rw [← FractionalIdeal.coeIdeal_mul]
      exact FractionalIdeal.mem_coeIdeal_of_mem A⁰ hra
    have hzra :
        z * algebraMap A K (algebraMap R₂ A r * a) ∈
          (J : Frac) := by
      have hmul := FractionalIdeal.mul_mem_mul hz hraFrac
      rw [← mul_assoc, hUinv_mul, one_mul] at hmul
      exact hmul
    have hmaprc :
        algebraMap A K (algebraMap R₂ A r * c) ∈
          (J : Frac) := by
      convert hzra using 1
      rw [map_mul, map_mul, hc]
      ring
    have hrc : algebraMap R₂ A r * c ∈ J := by
      obtain ⟨d, hd, hdc⟩ :=
        (FractionalIdeal.mem_coeIdeal A⁰).mp hmaprc
      have hdc' : d = algebraMap R₂ A r * c :=
        (IsFractionRing.injective A K) hdc
      rw [← hdc']
      exact hd
    have hcJ : c ∈ J := hJ r hr c hrc
    have hmapcJ : algebraMap A K c ∈ (J : Frac) :=
      FractionalIdeal.mem_coeIdeal_of_mem A⁰ hcJ
    convert hmapcJ using 1
    rw [hc]
    ring
  have hspan :
      FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) ≤
        (I : Frac) * (J : Frac) := by
    calc
      FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) =
          1 * FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) := by
            rw [one_mul]
      _ = ((I : Frac) * (↑U⁻¹ : Frac)) *
            FractionalIdeal.spanSingleton A⁰ (algebraMap A K a) := by
          rw [hU_mul_inv]
      _ = (I : Frac) *
            ((↑U⁻¹ : Frac) *
              FractionalIdeal.spanSingleton A⁰ (algebraMap A K a)) := by
          rw [mul_assoc]
      _ ≤ (I : Frac) * (J : Frac) :=
        mul_le_mul_right hInvSpan (I : Frac)
  have haFracProd : algebraMap A K a ∈ (I : Frac) * (J : Frac) :=
    hspan (FractionalIdeal.mem_spanSingleton_self A⁰ (algebraMap A K a))
  rw [← FractionalIdeal.coeIdeal_mul] at haFracProd
  obtain ⟨b, hb, hba⟩ :=
    (FractionalIdeal.mem_coeIdeal A⁰).mp haFracProd
  have hba' : b = a := (IsFractionRing.injective A K) hba
  simpa [hba'] using hb
end
end MazurProof.N13QuadraticTwoChartSpreadSaturation
end

end

theorem solution : type_of% @MazurProof.N13QuadraticTwoChartSpreadSaturation.mul_scalar_saturated_of_left_isUnit := @MazurProof.N13QuadraticTwoChartSpreadSaturation.mul_scalar_saturated_of_left_isUnit
