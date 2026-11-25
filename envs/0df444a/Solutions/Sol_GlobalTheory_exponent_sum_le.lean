-- Prove2me | solution 1 for GlobalTheory.exponent_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:21:03.232505+00:00
-- url     : https://prove2.me/submissions/3cc900c6-36ef-4aa4-b463-c6a6e40aaa4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExponentDivisorSumLe
import Theorems.Thm_GlobalTheory_exponent_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k f r : ℕ) (G N H a Q C : ℝ), 1 ≤ k → 1 ≤ r → 1 ≤ f → Real.log f ≤ Real.sqrt r → 1 ≤ G → 1 ≤ N → G ≤ H → N ≤ H → 0 ≤ a → 0 ≤ Q → Q * 9 ^ f ≤ H → 60 ≤ C → ∑ de ∈ Finset.Icc 1 ⌊G⌋₊, ((de : ℝ) / N) ^ (k - 1) * a * (Q * H ^ (11 + 3 * Real.logb 2 f)) * ((G / de) ^ ((k : ℝ) + Real.logb 2 (2 * f) + 1) * (N ^ (2 * r) * G ^ r * 9 ^ f * H ^ (9 + 9 * r + 16 * r ^ 2))) ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) := by
  intro k f r G N H a Q C hk hr hf hlog hG hN hGH hNH ha hQ hQH hC
  have hH0 : 0 < H := by linarith
  have hN0 : 0 < N := by linarith
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl0 : 0 ≤ Real.logb 2 (f : ℝ) := Real.logb_nonneg one_lt_two hf1
  have h2f : Real.logb 2 (2 * (f : ℝ)) = 1 + Real.logb 2 f := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt (by linarith)), Real.logb_self_eq_one one_lt_two]
  have hX : 0 ≤ a * (G / N) ^ k := mul_nonneg ha (pow_nonneg (div_nonneg (by linarith) hN0.le) _)

  refine le_trans (Finset.sum_le_sum (g := fun _ =>
    H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) * (a * (G / N) ^ k)) ?_) ?_
  · intro de hde
    rw [Finset.mem_Icc] at hde
    have hd1 : (1 : ℝ) ≤ de := by exact_mod_cast hde.1
    have hdG : (de : ℝ) ≤ G := le_trans (Nat.cast_le.mpr hde.2) (Nat.floor_le (by linarith))
    simp only [h2f]
    exact exponent_term k f r G N H a Q (Real.logb 2 f) de hk hG hN hGH hNH ha hQ hQH
      hl0 hd1 hdG
  ·
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have hfl : (⌊G⌋₊ : ℝ) ≤ H := (Nat.floor_le (by linarith)).trans hGH
    have hsq : Real.sqrt r ≤ r := by
      have h0 := Real.sqrt_nonneg (r : ℝ)
      have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ r by linarith)
      nlinarith
    have hlog2 := Real.log_two_gt_d9
    have hlb : Real.logb 2 (f : ℝ) ≤ 7 / 4 * r := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by linarith)
        (show (0 : ℝ) ≤ Real.log 2 - 0.69 by linarith)]
    have hexp : 1 + (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) ≤
        C * (r : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg (r : ℝ))]
    have hE0 : 0 ≤ H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) :=
      Real.rpow_nonneg hH0.le _
    calc (⌊G⌋₊ : ℝ) * (H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) *
            (a * (G / N) ^ k))
        ≤ H * (H ^ (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2) *
            (a * (G / N) ^ k)) := mul_le_mul_of_nonneg_right hfl (mul_nonneg hE0 hX)
      _ = H ^ (1 + (24 + 4 * Real.logb 2 (f : ℝ) + 12 * (r : ℝ) + 16 * (r : ℝ) ^ 2)) *
            (a * (G / N) ^ k) := by rw [Real.rpow_add hH0 1, Real.rpow_one]; ring
      _ ≤ H ^ (C * (r : ℝ) ^ 2) * (a * (G / N) ^ k) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp) hX
end GlobalTheory
