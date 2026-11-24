-- Prove2me | solution 1 for GlobalTheory.UU.le_of_pow_le_poly_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:43:33.112089+00:00
-- url     : https://prove2.me/submissions/160e262b-a38d-4f2f-a0cf-30b2ba3c2727

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LeOfPowLePolyMulPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution (A B K a g : ℕ)
    (H : ∀ k, A ^ k ≤ K * B ^ k * (1 + k * a) ^ g) : A ≤ B := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · have := H 1
    simp [hB] at this
    omega
  by_contra hAB
  push Not at hAB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hr : (1 : ℝ) < (A : ℝ) / B := by
    rw [one_lt_div hBr]; exact_mod_cast hAB
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt g hr).const_mul
    ((K : ℝ) * (1 + a) ^ g)
  rw [mul_zero] at ht
  have h1 : ∀ᶠ k : ℕ in Filter.atTop,
      (1 : ℝ) ≤ ((K : ℝ) * (1 + a) ^ g) * ((k : ℝ) ^ g / ((A : ℝ) / B) ^ k) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hk' : A ^ k ≤ K * B ^ k * ((1 + a) * k) ^ g := by
      refine (H k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
      nlinarith
    have hk2 : (A : ℝ) ^ k ≤ K * (B : ℝ) ^ k * ((1 + a) * k) ^ g := by exact_mod_cast hk'
    have hA : (0 : ℝ) < A := by exact_mod_cast (hB.trans hAB)
    rw [div_pow, ← mul_div_assoc, div_div_eq_mul_div, one_le_div (by positivity)]
    refine hk2.trans (le_of_eq ?_)
    rw [mul_pow]; ring
  have := ge_of_tendsto ht h1
  linarith
end GlobalTheory.UU
