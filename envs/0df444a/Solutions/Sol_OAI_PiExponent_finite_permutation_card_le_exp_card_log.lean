-- Prove2me | solution 1 for OAI.PiExponent.finite_permutation_card_le_exp_card_log
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T10:40:29.534745+00:00
-- url     : https://prove2.me/submissions/0166411f-103f-4db7-b23e-d0252635fa6f

import Mathlib.Tactic

open scoped BigOperators

lemma factorial_le_pow_self (n : ℕ) : n.factorial ≤ n ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.factorial_succ, Nat.pow_succ]
      calc
        (n + 1) * n.factorial ≤ (n + 1) * (n + 1) ^ n := by
          exact Nat.mul_le_mul_left _ (ih.trans (Nat.pow_le_pow_left (Nat.le_succ n) n))
        _ = (n + 1) ^ n * (n + 1) := by ac_rfl

theorem solution {α : Type*} [Fintype α] [DecidableEq α] :
    (Fintype.card (Equiv.Perm α) : ℝ) ≤
      Real.exp ((Fintype.card α : ℝ) * Real.log (Fintype.card α : ℝ)) := by
  let n := Fintype.card α
  rw [Fintype.card_perm]
  have hn : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    exact_mod_cast factorial_le_pow_self n
  by_cases h : n = 0
  · simp [n, h]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have hpow : (n : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log (n : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hnpos]
      simp [mul_comm]
    rw [← hpow]
    exact hn