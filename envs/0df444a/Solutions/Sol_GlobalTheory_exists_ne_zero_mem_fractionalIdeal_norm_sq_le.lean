-- Prove2me | solution 1 for GlobalTheory.exists_ne_zero_mem_fractionalIdeal_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:40.064991+00:00
-- url     : https://prove2.me/submissions/fa0c3314-ec17-48de-90d9-0f5be9ea1e6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Theorems.Thm_GlobalTheory_exists_ne_zero_mem_fractionalIdeal_place_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped nonZeroDivisors NNReal ENNReal
variable {E : Type*} [Field E] [NumberField E] [IsTotallyComplex E] {f : ℕ}
namespace GlobalTheory
theorem _root_.solution (hf : finrank ℚ E = 2 * f)
    (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : J ≠ 0) :
    ∃ a ∈ J, a ≠ 0 ∧ ∀ τ : E →+* ℂ, ‖τ a‖ ^ 2 ≤
      2 / Real.pi * ((FractionalIdeal.absNorm J : ℝ) * √|(discr E : ℝ)|) ^ ((f : ℝ)⁻¹) := by
  classical
  have hc : nrComplexPlaces E = f := by
    have := IsTotallyComplex.finrank E
    omega
  have hr : nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have hf0 : f ≠ 0 := by
    have : 0 < finrank ℚ E := finrank_pos
    omega
  set X : ℝ := (FractionalIdeal.absNorm J : ℝ) * √|(discr E : ℝ)| with hX
  have hN : (0 : ℝ) ≤ (FractionalIdeal.absNorm J : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg J
  have hX0 : 0 ≤ X := mul_nonneg hN (Real.sqrt_nonneg _)
  set B : ℝ := 2 / Real.pi * X ^ ((f : ℝ)⁻¹) with hB
  have hB0 : 0 ≤ B := by positivity
  let R : ℝ≥0 := ⟨√B, Real.sqrt_nonneg _⟩
  have hR : (R : ℝ) ^ 2 = B := Real.sq_sqrt hB0
  obtain ⟨a, ha, ha0, hle⟩ := exists_ne_zero_mem_fractionalIdeal_place_le E
    (Units.mk0 J hJ) (fun _ => R) (by
      rw [convexBodyLT_volume, minkowskiBound,
        volume_fundamentalDomain_fractionalIdealLatticeBasis,
        volume_fundamentalDomain_latticeBasis, mixedEmbedding.finrank,
        Finset.prod_pow_eq_pow_sum, sum_mult_eq, hf, convexBodyLTFactor, hc, hr]
      refine (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp (le_of_eq ?_)
      simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.coe_toReal,
        ENNReal.toReal_ofNat, Units.val_mk0, ENNReal.toReal_ofReal hN, pow_zero, one_mul,
        NNReal.coe_pow, NNReal.coe_real_pi, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
      rw [pow_mul (R : ℝ), hR, hB, mul_pow, Real.rpow_inv_natCast_pow hX0 hf0, hX, pow_mul,
        div_pow, show ((2 : ℝ) ^ 2) ^ f = 2 ^ f * 2 ^ f by rw [← mul_pow]; norm_num, inv_pow]
      have := Real.pi_pos
      field_simp)
  refine ⟨a, ha, ha0, fun τ => ?_⟩
  rw [← hR]
  have := hle (InfinitePlace.mk τ)
  rw [InfinitePlace.apply] at this
  exact pow_le_pow_left₀ (norm_nonneg _) this 2
end GlobalTheory
