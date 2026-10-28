-- Prove2me | solution 1 for LL_Decomp1528a.mertens1_small
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:27:38.089493+00:00
-- url     : https://prove2.me/submissions/d51e9915-fef9-48d3-809c-723764544ec2

import Mathlib

open Real Finset

theorem solution {x : ℝ} (hx : 1 ≤ x) (hx5 : x < 5) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ 2 := by
  have hfl : ⌊x⌋₊ ≤ 4 := by
    have : ⌊x⌋₊ < 5 := (Nat.floor_lt (by linarith)).2 (by exact_mod_cast hx5)
    omega
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ {2, 3} := by
    intro p hp
    simp only [Nat.primesLE, Nat.mem_primesBelow] at hp
    have : p < 5 := by omega
    interval_cases p <;> simp_all <;> norm_num at hp
  have hterm : ∀ p : ℕ, 0 ≤ log p / p ∧ log p / p ≤ 1 := by
    intro p
    refine ⟨div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p), ?_⟩
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp
    · have hp : (0:ℝ) < p := by exact_mod_cast h
      rw [div_le_one hp]
      linarith [Real.log_le_sub_one_of_pos hp]
  have hS0 : 0 ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p := sum_nonneg fun p _ => (hterm p).1
  have hS2 : ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p ≤ 2 := by
    calc ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p ≤ ∑ p ∈ ({2, 3} : Finset ℕ), log p / p :=
          sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => (hterm p).1)
      _ ≤ 2 := by
        rw [sum_pair (by norm_num)]
        linarith [(hterm 2).2, (hterm 3).2]
  have hl0 : 0 ≤ log x := Real.log_nonneg hx
  have hl2 : log x ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (x := x / 3) (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at this
    have h3 : log 3 < 1.11 := by
      have := Real.log_le_sub_one_of_pos (x := 3 / Real.exp 1) (by positivity)
      rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at this
      have : 3 / Real.exp 1 < 1.1037 := by
        rw [div_lt_iff₀ (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
      linarith
    linarith
  rw [abs_le]; constructor <;> linarith
