-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_positive_monotone_grid_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:50:08.615789+00:00
-- url     : https://prove2.me/submissions/98528375-5e74-4df4-a335-209aa256b935

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false

/-- A one-sided monotone path has at most its endpoint envelope
as total variation on an arbitrary finite grid. -/
theorem solution
    (g : Nat → Real) (n : Nat) (C : Real)
    (hMono : Monotone g ∨ Antitone g)
    (h0 : 0 ≤ g 0) (hn : 0 ≤ g n)
    (hb0 : g 0 ≤ C) (hbn : g n ≤ C) :
    (∑ i ∈ Finset.range n, |g (i + 1) - g i|) ≤ C := by
  rcases hMono with hm | hm
  · have ht (k : Nat) :
        (∑ i ∈ Finset.range k, (g (i + 1) - g i)) = g k - g 0 := by
      induction k with
      | zero => simp
      | succ k ih => rw [Finset.sum_range_succ, ih]; ring
    calc
      (∑ i ∈ Finset.range n, |g (i + 1) - g i|)
          = ∑ i ∈ Finset.range n, (g (i + 1) - g i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_of_nonneg (sub_nonneg.mpr (hm (Nat.le_succ i)))]
      _ = g n - g 0 := ht n
      _ ≤ C := by linarith
  · have ht (k : Nat) :
        (∑ i ∈ Finset.range k, (g i - g (i + 1))) = g 0 - g k := by
      induction k with
      | zero => simp
      | succ k ih => rw [Finset.sum_range_succ, ih]; ring
    calc
      (∑ i ∈ Finset.range n, |g (i + 1) - g i|)
          = ∑ i ∈ Finset.range n, (g i - g (i + 1)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hm (Nat.le_succ i)))]
      _ = g 0 - g n := ht n
      _ ≤ C := by linarith
