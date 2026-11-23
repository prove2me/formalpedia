-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.nonnegative_multiplicative_survival_positive_one_of_small_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:36:41.704807+00:00
-- url     : https://prove2.me/submissions/2e759aa1-4d07-4574-b87c-f521db464941

import Mathlib
set_option autoImplicit false
open Set Filter Topology

theorem solution
    (S : ℝ → ℝ)
    (hsemi : ∀ a b : ℝ, 0 < a → 0 < b → S (a + b) = S a * S b)
    (hnon : ∀ a : ℝ, 0 < a → 0 ≤ S a)
    (d : ℝ) (hd : 0 < d) (hSd : 0 < S d) :
    0 < S 1 := by
  have hmultiple (n : ℕ) : 0 < S (((n + 1 : ℕ) : ℝ) * d) := by
    induction n with
    | zero => simpa using hSd
    | succ n ih =>
      have harg : 0 < (((n + 1 : ℕ) : ℝ) * d) :=
        mul_pos (by exact_mod_cast Nat.succ_pos n) hd
      have hstep := hsemi (((n + 1 : ℕ) : ℝ) * d) d harg hd
      have heq : (((n + 1 + 1 : ℕ) : ℝ) * d) =
          (((n + 1 : ℕ) : ℝ) * d) + d := by push_cast; ring
      rw [heq, hstep]
      exact mul_pos ih hSd
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / d)
  have hnd : 1 < (n : ℝ) * d := by
    have hne : d ≠ 0 := ne_of_gt hd
    have h := mul_lt_mul_of_pos_right hn hd
    rwa [one_div_mul_cancel hne] at h
  cases n with
  | zero => norm_num at hnd
  | succ n =>
    let r : ℝ := (((n + 1 : ℕ) : ℝ) * d) - 1
    have hr : 0 < r := by dsimp [r]; simpa using hnd
    have hsum : (1 : ℝ) + r = (((n + 1 : ℕ) : ℝ) * d) := by
      dsimp [r]; ring
    have hprod : 0 < S 1 * S r := by
      have h := hmultiple n
      rw [← hsum] at h
      rw [hsemi 1 r zero_lt_one hr] at h
      exact h
    by_contra hnonpos
    have hle : S 1 ≤ 0 := le_of_not_gt hnonpos
    exact (not_le_of_gt hprod)
      (mul_nonpos_of_nonpos_of_nonneg hle (hnon r hr))
