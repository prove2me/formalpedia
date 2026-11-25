-- Prove2me | solution 1 for GlobalTheory.JetConstSq.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:58.975318+00:00
-- url     : https://prove2.me/submissions/26c144af-87f6-4514-b413-9fea6fe55fd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ImportsAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.JetConstSq
namespace GlobalTheory.JetConstSq
theorem _root_.solution : ∀ C₃ CΛ C₀ C₂ : ℝ, 0 ≤ C₃ → 0 ≤ CΛ → 0 ≤ C₀ → 0 < C₂ → ∃ C₄ : ℝ, ∀ (b Λ : ℝ) (r n₀ p₀ : ℕ), 3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * r + 2 : ℕ) : ℝ)) → n₀ ≤ 30 * (r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((r : ℝ) + 1) ^ 2 → 2 * (3 * b) ^ (2 * n₀) * (1 * (C₂ * Λ ^ 2) ^ (r + 1)) * b ^ (2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ)) ≤ b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by
  intro C₃ CΛ C₀ C₂ h3 hΛ h0 h2
  refine ⟨40 + CΛ + C₂ + 2 * C₃ * (C₀ + 9), ?_⟩
  intro b Λ r n₀ p₀ hb hΛ1 hΛb hn hp
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hnR : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn
  have hm : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have hq : ((2 * p₀ + n₀ : ℕ) : ℝ) = 2 * (p₀ : ℝ) + n₀ := by push_cast; ring
  have hr : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  rw [hm] at hΛb
  rw [hm, hq]
  have hs : (1 : ℝ) ≤ (r : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith

  have hC2 : C₂ ≤ b ^ C₂ := by
    have h1 : (1 : ℝ) ≤ Real.log b := by
      rw [Real.le_log_iff_exp_le hb0]
      have := Real.exp_one_lt_d9
      linarith
    rw [Real.rpow_def_of_pos hb0]
    have h4 : C₂ ≤ Real.log b * C₂ := by nlinarith
    have := Real.add_one_le_exp (Real.log b * C₂)
    linarith
  have e1 : (2 : ℝ) ≤ b ^ (1 : ℝ) := by rw [Real.rpow_one]; linarith
  have e2 : (3 * b) ^ (2 * n₀) ≤ b ^ (4 * (n₀ : ℝ)) := by
    have : (3 * b) ^ (2 * n₀) ≤ (b * b) ^ (2 * n₀) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    refine this.trans (le_of_eq ?_)
    rw [show (4 * (n₀ : ℝ)) = ((4 * n₀ : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  have e3 : 1 * (C₂ * Λ ^ 2) ^ (r + 1) ≤
      b ^ ((C₂ + 2 * (CΛ * (2 * ((r : ℝ) + 1)))) * ((r : ℝ) + 1)) := by
    rw [one_mul, Real.rpow_mul hb0.le, ← hr, Real.rpow_natCast]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [Real.rpow_add hb0, mul_comm (2 : ℝ) (CΛ * _), Real.rpow_mul hb0.le, Real.rpow_two, hr]
    exact mul_le_mul hC2 (pow_le_pow_left₀ (by linarith) hΛb 2) (by positivity) (by positivity)
  generalize ((r : ℝ) + 1) = s at *
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  have hs2 : 1 ≤ s ^ 2 := one_le_pow₀ hs
  have hs12 : s ≤ s ^ 2 := by nlinarith
  have hs4 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  calc _ ≤ b ^ (1 : ℝ) * b ^ (4 * (n₀ : ℝ)) * b ^ ((C₂ + 2 * (CΛ * (2 * s))) * s) *
        b ^ (2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀)) := by
        gcongr
    _ = b ^ (1 + 4 * (n₀ : ℝ) + (C₂ + 2 * (CΛ * (2 * s))) * s +
        2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀)) := by
        rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0]
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb1
        have a1 : 1 + 4 * (n₀ : ℝ) ≤ 40 * (2 * s) ^ 4 := by nlinarith
        have a2 : C₂ * s ≤ C₂ * (2 * s) ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ h2.le; nlinarith
        have a3 : CΛ * (4 * s ^ 2) ≤ CΛ * (2 * s) ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ hΛ; nlinarith
        have a4 : 2 * (p₀ : ℝ) + n₀ ≤ (C₀ + 9) * (2 * s) ^ 2 := by
          have : 0 ≤ C₀ * s ^ 2 := by positivity
          nlinarith
        have a5 : 2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀) ≤
            2 * C₃ * (2 * s) ^ 2 * ((C₀ + 9) * (2 * s) ^ 2) :=
          mul_le_mul_of_nonneg_left a4 (by positivity)
        nlinarith
end GlobalTheory.JetConstSq
