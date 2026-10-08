-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.integer_branch_coefficients_affine
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T17:19:41.063505+00:00
-- url     : https://prove2.me/submissions/2d8fe6be-daf3-463f-8002-d6a3d7f40c74

import Mathlib

theorem solution
    (a x : ℝ) (m : ℕ) (hx : ∃ n : ℕ, x = n) :
    ∀ s ∈ Set.Icc (m : ℝ) (m + 1),
      a * min s x =
        (if x ≤ (m : ℝ) then a * x else 0) +
          (if (m : ℝ) < x then a else 0) * s := by
  rcases hx with ⟨n, rfl⟩
  intro s hs
  by_cases hmn : m < n
  · have hmn' : m + 1 ≤ n := by omega
    have hupper : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn'
    have hsn : s ≤ (n : ℝ) := le_trans hs.2 hupper
    have hmx : ¬ (n : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.not_le_of_gt hmn)
    simp [min_eq_left hsn, hmx, hmn]
  · have hnm : n ≤ m := Nat.le_of_not_gt hmn
    have hlower : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    have hns : (n : ℝ) ≤ s := le_trans hlower hs.1
    have hmx : ¬ (m : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.not_lt_of_ge hnm)
    simp [min_eq_right hns, hmx, hnm]
