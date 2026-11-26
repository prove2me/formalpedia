-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_stopped_grid_crossing_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:32:28.739123+00:00
-- url     : https://prove2.me/submissions/96fafc9d-cc73-460e-a59b-3b1355884170

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- A monotone grid has at most one cell strictly crossing a fixed time. -/
theorem solution (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ) (t : NNReal) :
    ((Finset.range n).filter (fun k => u k < t ∧ t < u (k+1))).card ≤ 1 := by
  classical
  let S := (Finset.range n).filter (fun k => u k < t ∧ t < u (k+1))
  change S.card ≤ 1
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact (not_lt_of_ge (hu (Nat.succ_le_of_lt hlt))) (hb'.1.trans ha'.2)
  · exact (not_lt_of_ge (hu (Nat.succ_le_of_lt hgt))) (ha'.1.trans hb'.2)
