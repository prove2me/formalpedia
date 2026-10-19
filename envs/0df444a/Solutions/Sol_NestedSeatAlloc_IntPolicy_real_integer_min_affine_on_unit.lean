-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.real_integer_min_affine_on_unit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:23:27.492307+00:00
-- url     : https://prove2.me/submissions/8622752b-3ce2-4e4d-a6ef-003b48b1eeb2

import Mathlib
set_option autoImplicit false

theorem solution
    (a x : ℝ) (m : ℕ) (hx : ∃ n : ℕ, x = n) :
    ∃ c d : ℝ, ∀ s ∈ Set.Icc (m : ℝ) (m + 1),
      a * min s x = c + d * s := by
  obtain ⟨n, rfl⟩ := hx
  by_cases h : n ≤ m
  · refine ⟨a * n, 0, fun s hs => ?_⟩
    have h1 : (n : ℝ) ≤ m := by exact_mod_cast h
    rw [min_eq_right (h1.trans hs.1)]
    ring
  · refine ⟨0, a, fun s hs => ?_⟩
    have h1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : m + 1 ≤ n)
    rw [min_eq_left (hs.2.trans h1)]
    ring
