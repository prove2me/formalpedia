-- Prove2me | solution 1 for LL_Decomp1528a.sum_log_div_pp1_split
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:30:08.793896+00:00
-- url     : https://prove2.me/submissions/dd471cbf-4863-4fde-8330-3c53d2230d51

import Mathlib

open Real Finset

theorem solution (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ p ∈ Nat.primesLE 1000, log p / ((p : ℝ) * ((p : ℝ) - 1)) +
        ∑ m ∈ Ioc 1000 n, log m / ((m : ℝ) * ((m : ℝ) - 1)) := by
  have hnn : ∀ m : ℕ, 0 ≤ log m / ((m : ℝ) * ((m : ℝ) - 1)) := by
    intro m
    apply div_nonneg (Real.log_natCast_nonneg m)
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have : (1:ℝ) ≤ m := by exact_mod_cast h
      nlinarith
  rw [← sum_filter_add_sum_filter_not (Nat.primesLE n) (fun p => p ≤ 1000)]
  refine add_le_add ?_ ?_
  · apply sum_le_sum_of_subset_of_nonneg _ (fun m _ _ => hnn m)
    intro p hp
    rw [mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
    rw [Nat.primesLE, Nat.mem_primesBelow]
    exact ⟨by omega, hp.1.2⟩
  · apply sum_le_sum_of_subset_of_nonneg _ (fun m _ _ => hnn m)
    intro p hp
    rw [mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
    rw [mem_Ioc]
    omega
