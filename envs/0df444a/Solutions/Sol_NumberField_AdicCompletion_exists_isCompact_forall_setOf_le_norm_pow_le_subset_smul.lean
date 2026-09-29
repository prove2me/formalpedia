-- Prove2me | solution 1 for NumberField.AdicCompletion.exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cc8c819a-270d-51bb-807a-dfc0398f6e08

import Mathlib
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdicCompletion_exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 < R) :
    ∃ B : Set (v.adicCompletion K), IsCompact B ∧ (0 : v.adicCompletion K) ∉ B ∧
      ∀ a : ℝ, 0 < a → ∃ x₀ : v.adicCompletion K, x₀ ≠ 0 ∧
        {x : v.adicCompletion K | a ≤ ‖x‖ ^ n ∧ ‖x‖ ^ n ≤ a * R} ⊆ x₀ • B := by
  haveI : ProperSpace (v.adicCompletion K) := NumberField.AdelicHaar.properSpace_adicCompletion (𝓞 K) K v
  refine ⟨{y : v.adicCompletion K | R⁻¹ ≤ ‖y‖ ^ n ∧ ‖y‖ ^ n ≤ R}, ?_, ?_, ?_⟩
  · have hcl : IsClosed {y : v.adicCompletion K | R⁻¹ ≤ ‖y‖ ^ n ∧ ‖y‖ ^ n ≤ R} :=
      (isClosed_le continuous_const (continuous_norm.pow n)).inter
        (isClosed_le (continuous_norm.pow n) continuous_const)
    refine (isCompact_closedBall (0 : v.adicCompletion K) (max R 1)).of_isClosed_subset hcl ?_
    rintro y ⟨-, hy⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    push Not at h
    have h1 : 1 < ‖y‖ := (le_max_right _ _).trans_lt h
    have h2 : ‖y‖ ≤ ‖y‖ ^ n := le_self_pow₀ h1.le hn.ne'
    linarith [le_max_left R 1]
  · rintro ⟨h, -⟩
    rw [norm_zero, zero_pow hn.ne'] at h
    exact absurd h (not_le.2 (inv_pos.2 hR))
  · intro a ha
    by_cases hex : ∃ x₀ : v.adicCompletion K, a ≤ ‖x₀‖ ^ n ∧ ‖x₀‖ ^ n ≤ a * R
    · obtain ⟨x₀, h₀, h₀'⟩ := hex
      have hx₀ : x₀ ≠ 0 := by
        rintro rfl
        rw [norm_zero, zero_pow hn.ne'] at h₀
        linarith
      have hx₀n : 0 < ‖x₀‖ ^ n := pow_pos (norm_pos_iff.2 hx₀) n
      refine ⟨x₀, hx₀, fun x hx => ?_⟩
      obtain ⟨hx, hx'⟩ := hx
      refine Set.mem_smul_set.2 ⟨x₀⁻¹ * x, ⟨?_, ?_⟩, by rw [smul_eq_mul, mul_inv_cancel_left₀ hx₀]⟩
      · rw [norm_mul, norm_inv, mul_pow, inv_pow, ← div_eq_inv_mul, le_div_iff₀ hx₀n]
        calc R⁻¹ * ‖x₀‖ ^ n ≤ R⁻¹ * (a * R) := mul_le_mul_of_nonneg_left h₀' (inv_nonneg.2 hR.le)
          _ = a := by field_simp
          _ ≤ ‖x‖ ^ n := hx
      · rw [norm_mul, norm_inv, mul_pow, inv_pow, ← div_eq_inv_mul, div_le_iff₀ hx₀n]
        calc ‖x‖ ^ n ≤ a * R := hx'
          _ ≤ ‖x₀‖ ^ n * R := mul_le_mul_of_nonneg_right h₀ hR.le
          _ = R * ‖x₀‖ ^ n := mul_comm _ _
    · exact ⟨1, one_ne_zero, fun x hx => (hex ⟨x, hx⟩).elim⟩

end S_NumberField_AdicCompletion_exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul
end P2MW
export P2MW.S_NumberField_AdicCompletion_exists_isCompact_forall_setOf_le_norm_pow_le_subset_smul (solution)
