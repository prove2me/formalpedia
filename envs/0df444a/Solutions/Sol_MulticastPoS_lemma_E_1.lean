-- Prove2me | solution 1 for MulticastPoS.lemma_E_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:31:21.399451+00:00
-- url     : https://prove2.me/submissions/1826a469-d4f3-4fa8-9d5f-f7ee97ac039b

import Mathlib

theorem solution :
    (harmonic 32 : ℝ) < 5 ∧
      ∀ L : ℕ, 4 ≤ L → (harmonic (8 * L ^ 2) : ℝ) ≤ 5 * harmonic L := by
  constructor
  · have h : harmonic 32 < 5 := by
      norm_num [harmonic, Finset.sum_range_succ]
    exact_mod_cast h
  · intro L hL
    have h1 := harmonic_le_one_add_log (8 * L ^ 2)
    have h2 := log_add_one_le_harmonic L
    push_cast at h1 h2
    have hL4 : (4:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
    have hLp : (0:ℝ) < (L:ℝ) := by linarith
    have h3 : (24:ℝ) ≤ ((L:ℝ) + 1) ^ 3 := by nlinarith
    have h4 : (L:ℝ) ^ 2 ≤ ((L:ℝ) + 1) ^ 2 := by nlinarith
    have h5 : 24 * (L:ℝ) ^ 2 ≤ ((L:ℝ) + 1) ^ 5 := by
      have := mul_le_mul h4 h3 (by norm_num) (by positivity)
      nlinarith
    have he := Real.exp_one_lt_d9
    have h6 : Real.exp 1 * (8 * (L:ℝ) ^ 2) ≤ ((L:ℝ) + 1) ^ 5 := by
      have : 0 ≤ (L:ℝ) ^ 2 := by positivity
      nlinarith
    have h7 := Real.log_le_log (by positivity) h6
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow] at h7
    push_cast at h7
    linarith
