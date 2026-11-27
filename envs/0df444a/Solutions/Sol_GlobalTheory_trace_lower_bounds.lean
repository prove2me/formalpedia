-- Prove2me | solution 1 for GlobalTheory.trace_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:24.58082+00:00
-- url     : https://prove2.me/submissions/c4a0ef05-79ae-40d4-baf8-bf6bccf590d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_eq_zero_of_isIntegral_of_sum_norm_lt
import Theorems.Thm_GlobalTheory_finrank_mul_absNorm_rpow_le_sum_sq
import Theorems.Thm_GlobalTheory_finrank_mul_discr_rpow_le_sum_sq
import Theorems.Thm_GlobalTheory_eq_zero_of_embedding_eq_zero
import Theorems.Thm_GlobalTheory_trace_mem_of_mem_traceDual
import Theorems.Thm_GlobalTheory_finrank_mul_norm_rpow_le_trace
import Theorems.Thm_GlobalTheory_finrank_le_trace_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (F K : Type*) [Field F] [NumberField F] [IsTotallyReal F]
    [Field K] [NumberField K] :
    (∀ a : F, (∀ σ : F →+* ℝ, 0 < σ a) →
      (finrank ℚ F : ℝ) * ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (1 / (finrank ℚ F : ℝ))
        ≤ ((Algebra.trace ℚ F a : ℚ) : ℝ)) ∧
    (∀ a : F, IsIntegral ℤ a → (∀ σ : F →+* ℝ, 0 < σ a) →
      (finrank ℚ F : ℚ) ≤ Algebra.trace ℚ F a) ∧
    (∀ a : K, IsIntegral ℤ a → ∑ σ : K →+* ℂ, ‖σ a‖ < finrank ℚ K → a = 0) ∧
    (∀ x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹, x ≠ 0 →
      (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
        ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2) ∧
    (∀ (J : FractionalIdeal (𝓞 K)⁰ K), ∀ x ∈ J, x ≠ 0 →
      (finrank ℚ K : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ (2 / (finrank ℚ K : ℝ))
        ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2) ∧
    (∀ (a : F) (σ : F →+* ℝ), σ a = 0 → a = 0) ∧
    (∀ q : ℚ, q ≠ 0 → ∀ x ∈ Submodule.traceDual ℤ ℚ (Submodule.span (𝓞 F) {(q : F)}),
      ∃ m : ℤ, Algebra.trace ℚ F x = q⁻¹ * m) :=
  ⟨fun _ ha => finrank_mul_norm_rpow_le_trace ha,
    fun _ hi ha => finrank_le_trace_of_isIntegral hi ha,
    fun _ hi h => eq_zero_of_isIntegral_of_sum_norm_lt hi h,
    fun _ hx h0 => finrank_mul_discr_rpow_le_sum_sq hx h0,
    fun _ _ hx h0 => finrank_mul_absNorm_rpow_le_sum_sq hx h0,
    fun _ σ h => eq_zero_of_embedding_eq_zero σ h,
    fun _ hq _ hx => trace_mem_of_mem_traceDual hq hx⟩
end GlobalTheory
