-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_partition_threshold_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:18:55.135872+00:00
-- url     : https://prove2.me/submissions/5e15567b-1e20-4e0c-96f3-ffb66f19502d

import Mathlib
open Set Filter
open scoped Topology ENNReal NNReal
set_option autoImplicit false
/-- Induct on the grid length, using monotonicity and telescoping consecutive values. -/
theorem solution
    (p : ℕ → ℝ) (hp : Monotone p) (Y : ℝ → ℝ)
    (n : ℕ) (s : ℝ) (h0 : p 0 ≤ s) (hn : s < p n) :
    ∃ j < n, p j ≤ s ∧ s < p (j+1) ∧
      (∑ i ∈ Finset.range (n+1),
        (if i=0 then Y (p 0) else Y (p i)-Y (p (i-1))) *
        (if p i ≤ s then (1:ℝ) else 0)) = Y (p j) := by
  let c : ℕ → ℝ := fun i => if i=0 then Y (p 0) else Y (p i)-Y (p (i-1))
  have htel : ∀ k : ℕ, (∑ i ∈ Finset.range (k+1), c i) = Y (p k) := by
    intro k
    induction k with
    | zero => simp [c]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp [c]
  change ∃ j < n, p j ≤ s ∧ s < p (j+1) ∧
    (∑ i ∈ Finset.range (n+1), c i * (if p i ≤ s then (1:ℝ) else 0)) = Y (p j)
  induction n with
  | zero => exact (not_lt_of_ge h0 hn).elim
  | succ n ih =>
    by_cases h : s < p n
    · obtain ⟨j,hj,hjs,hsj,he⟩ := ih h
      refine ⟨j, Nat.lt_succ_of_lt hj, hjs, hsj, ?_⟩
      rw [Finset.sum_range_succ, he, if_neg (not_le_of_gt hn), mul_zero, add_zero]
    · have hpn : p n ≤ s := le_of_not_gt h
      refine ⟨n, Nat.lt_succ_self n, hpn, hn, ?_⟩
      rw [Finset.sum_range_succ, if_neg (not_le_of_gt hn), mul_zero, add_zero]
      calc
        _ = ∑ i ∈ Finset.range (n+1), c i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hle : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          rw [if_pos ((hp hle).trans hpn), mul_one]
        _ = _ := htel n
