-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_nonnegative_majorant_below_of_finite_strict_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:54:09.705647+00:00
-- url     : https://prove2.me/submissions/876fd6dc-1cb0-4792-a895-d325951051cf

import Mathlib

theorem solution {d : Nat} (x : Fin d → Real) {c : Real} (hc : 0 < c) (hx : ∀ i, x i < c) : ∃ M : Real, 0 ≤ M ∧ (∀ i, x i ≤ M) ∧ M < c := by
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · exact ⟨0, le_rfl, fun i => isEmptyElim i, hc⟩
  · obtain ⟨j, hj⟩ := Finite.exists_max x
    exact ⟨max 0 (x j), le_max_left _ _, fun i => (hj i).trans (le_max_right _ _),
      max_lt hc (hx j)⟩
