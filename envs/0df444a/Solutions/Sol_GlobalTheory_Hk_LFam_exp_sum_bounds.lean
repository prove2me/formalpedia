-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.exp_sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:27:15.140376+00:00
-- url     : https://prove2.me/submissions/5eb0082f-7da4-45fa-8c79-9deb6f63c74f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
import Theorems.Thm_GlobalTheory_Hk_LFam_summable_norm_aChi_exp
import Theorems.Thm_GlobalTheory_Hk_LFam_norm_theta_large
import Theorems.Thm_GlobalTheory_Hk_LFam_norm_theta_small
import Theorems.Thm_GlobalTheory_Hk_LFam_integral_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
namespace LFam
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), (∀ t : ℝ, 0 < t → Summable (fun n : ℕ => ‖𝓕.aChi χ n‖ * Real.exp (-(t * n))) ∧ ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) - 𝓕.res χ / t‖ ≤ C * 𝓕.B ^ 11 * min t (1 / t)) ∧ (χ ≠ 1 → (∀ t : ℝ, 1 ≤ t → ‖∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ)‖ ≤ C * 𝓕.B * Real.exp (-(t / 2))) ∧ ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ, 𝓕.aChi χ n * (Real.exp (-(t * n)) : ℂ) = 𝓕.F χ 1) := by
  set S : ℝ := 14 * ∑' n : ℕ, (n : ℝ) * Real.exp (-(1 / 2 * n)) with hS
  have hS0 : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun n => by positivity)
  refine ⟨2 * S + 4, by positivity, fun 𝓕 χ => ⟨fun t ht => ⟨𝓕.summable_norm_aChi_exp χ ht, ?_⟩,
    fun hχ => ⟨fun t ht => ?_, 𝓕.integral_theta χ hχ⟩⟩⟩
  · have hB : 1 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
    rcases le_total t 1 with h1 | h1
    · have : t ≤ 1 / t := by rw [le_div_iff₀ ht]; nlinarith
      rw [min_eq_left this]
      refine (𝓕.norm_theta_small χ ht h1).trans ?_
      have : 0 ≤ 𝓕.B ^ 11 * t := by positivity
      nlinarith
    · have : 1 / t ≤ t := by rw [div_le_iff₀ ht]; nlinarith
      rw [min_eq_right this]
      have e1 : Real.exp (-(t / 2)) ≤ 2 * (1 / t) := by
        have := Real.add_one_le_exp (t / 2)
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
        have e : (2 * (1 / t))⁻¹ = t / 2 := by field_simp
        linarith
      have hκ : 0 ≤ 𝓕.κ := le_trans (by positivity) 𝓕.κ_ge
      have e2 : ‖𝓕.res χ‖ ≤ 4 * 𝓕.B := by
        unfold LFam.res
        split_ifs
        · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul 𝓕.κ_le 𝓕.card_le (by positivity) (by norm_num)
        · rw [norm_zero]; positivity
      have e3 : 𝓕.B ≤ 𝓕.B ^ 11 := le_self_pow₀ hB (by norm_num)
      calc _ ≤ S * 𝓕.B * Real.exp (-(t / 2)) + ‖𝓕.res χ‖ * (1 / t) := by
            refine (norm_sub_le _ _).trans (add_le_add (𝓕.norm_theta_large χ h1) (le_of_eq ?_))
            rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le, mul_one_div]
        _ ≤ S * 𝓕.B * (2 * (1 / t)) + 4 * 𝓕.B * (1 / t) := by gcongr
        _ = (2 * S + 4) * 𝓕.B * (1 / t) := by ring
        _ ≤ _ := by gcongr
  · have hB : 0 ≤ 𝓕.B := le_trans (by norm_num) 𝓕.B_ge
    refine (𝓕.norm_theta_large χ ht).trans ?_
    gcongr
    linarith
end LFam
end GlobalTheory.Hk
