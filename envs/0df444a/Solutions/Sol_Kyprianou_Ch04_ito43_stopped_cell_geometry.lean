-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_stopped_cell_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:26:42.025797+00:00
-- url     : https://prove2.me/submissions/1ea868e5-396c-4ed5-8b40-c9dfe6d69ab7

import Mathlib
open Set
set_option autoImplicit false

/-- A monotone grid has at most one cell cut strictly in its interior by a stop. -/
theorem solution (u : ℕ → ℝ) (hu : Monotone u) (t : ℝ) (i j : ℕ)
    (hi : u i < t ∧ t < u (i+1)) (hj : u j < t ∧ t < u (j+1)) :
    i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with hij | hji
  · exact (not_lt_of_ge (hu (Nat.succ_le_of_lt hij))) (hj.1.trans hi.2)
  · exact (not_lt_of_ge (hu (Nat.succ_le_of_lt hji))) (hi.1.trans hj.2)
