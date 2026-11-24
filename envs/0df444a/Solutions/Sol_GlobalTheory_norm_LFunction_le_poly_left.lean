-- Prove2me | solution 1 for GlobalTheory.norm_LFunction_le_poly_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:17:57.159479+00:00
-- url     : https://prove2.me/submissions/7f39f493-2f3b-4a5f-9241-6a6521cf5fa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
import Theorems.Thm_GlobalTheory_LLeft_norm_diffPow_le
import Theorems.Thm_GlobalTheory_LLeft_summable_nine_pow_mul_inv_sq_succ
import Theorems.Thm_GlobalTheory_LLeft_norm_term_le
import Theorems.Thm_GlobalTheory_LLeft_LFunction_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open LLeft
namespace GlobalTheory
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ,
      -(7/4 : ℝ) ≤ s.re → ‖LFunction χ s‖ ≤ C * (q : ℝ) ^ 4 * (‖s‖ + 2) ^ 4 := by
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(9 / 8 : ℝ)) with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  refine ⟨15 + 64 * Z, by positivity, fun q _ χ hχ s hs => ?_⟩
  obtain ⟨b, μ₁, μ₂, μ₃, hb, m₁, m₂, m₃, he⟩ := LFunction_eq q χ hχ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hn := norm_nonneg s
  set A : ℝ := (q : ℝ) ^ 4 with hA
  set B : ℝ := (‖s‖ + 2) ^ 4 with hB
  have q1 : (q : ℝ) ≤ A := by simpa using pow_le_pow_right₀ hq (show 1 ≤ 4 by norm_num)
  have q2 : (q : ℝ) ^ 2 ≤ A := pow_le_pow_right₀ hq (by norm_num)
  have q3 : (q : ℝ) ^ 3 ≤ A := pow_le_pow_right₀ hq (by norm_num)
  have hA0 : 0 ≤ A := by positivity
  have hs1 : 1 ≤ ‖s‖ + 2 := by linarith
  have b0 : 1 ≤ B := one_le_pow₀ hs1
  have b2 : (‖s‖ + 2) ^ 2 ≤ B := pow_le_pow_right₀ hs1 (by norm_num)
  have b3 : (‖s‖ + 3) ^ 3 ≤ 8 * B := by
    calc (‖s‖ + 3) ^ 3 ≤ (2 * (‖s‖ + 2)) ^ 3 := by gcongr; linarith
      _ = 8 * (‖s‖ + 2) ^ 3 := by ring
      _ ≤ 8 * B := by gcongr; exact pow_le_pow_right₀ hs1 (by norm_num)
  have t0 : ‖diffPow 0 s 1‖ ≤ B := by simpa [diffPow] using b0
  have t1 : ‖diffPow 1 s 1‖ ≤ 5 * B := by
    have h1 : ‖diffPow 0 s 1‖ ≤ 1 := by simp [diffPow]
    have h2 : ‖diffPow 0 s (1 + 1)‖ ≤ 4 := by
      rw [diffPow, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      calc ((1 : ℝ) + 1) ^ (-s).re ≤ (1 + 1) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simp only [neg_re]; linarith)
        _ = 4 := by norm_num
    rw [diffPow]
    linarith [norm_sub_le (diffPow 0 s 1) (diffPow 0 s (1 + 1))]
  have t2 : ‖diffPow 2 s 1‖ ≤ B := by
    have := norm_diffPow_le 2 s 1 one_pos (by push_cast; linarith)
    simp only [Real.one_rpow, mul_one, Nat.cast_ofNat] at this
    linarith
  have t3 : ‖∑' n : ℕ, b n * diffPow 3 s ((n : ℝ) + 1)‖ ≤ 8 * (q : ℝ) ^ 3 * (‖s‖ + 3) ^ 3 * Z := by
    rw [hZ, ← tsum_mul_left]
    exact tsum_of_norm_bounded ((summable_nine_pow_mul_inv_sq_succ (9 / 8) (by norm_num)).mul_left _).hasSum
      fun n => norm_term_le b _ _ hb s (by linarith) le_rfl n
  have u0 : ‖μ₁ * diffPow 0 s 1‖ ≤ A * B := by
    rw [norm_mul]; exact mul_le_mul (m₁.trans q1) t0 (norm_nonneg _) hA0
  have u1 : ‖μ₂ * diffPow 1 s 1‖ ≤ (2 * A) * (5 * B) := by
    rw [norm_mul]; exact mul_le_mul (by linarith) t1 (norm_nonneg _) (by positivity)
  have u2 : ‖μ₃ * diffPow 2 s 1‖ ≤ (4 * A) * B := by
    rw [norm_mul]; exact mul_le_mul (by linarith) t2 (norm_nonneg _) (by positivity)
  have u3 : 8 * (q : ℝ) ^ 3 * (‖s‖ + 3) ^ 3 * Z ≤ 8 * A * (8 * B) * Z := by gcongr
  rw [he s (by linarith)]
  refine (norm_add_le _ _).trans ?_
  have := norm_add₃_le (a := μ₁ * diffPow 0 s 1) (b := μ₂ * diffPow 1 s 1)
    (c := μ₃ * diffPow 2 s 1)
  nlinarith
end GlobalTheory
