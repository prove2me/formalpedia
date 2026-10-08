-- Prove2me | solution 1 for NewMinimalStandardModel.singlet_quartic_nondecreasing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:43:46.744041+00:00
-- url     : https://prove2.me/submissions/6140f434-e962-464d-838b-015b0eb8f05c

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

open NewMinimalStandardModel in
theorem solution (h k : ℝ → ℝ) (a b : ℝ)
    (hODE : ∀ t ∈ Set.Icc a b,
      HasDerivAt h ((3 * h t ^ 2 + 12 * k t ^ 2) / (4 * Real.pi) ^ 2) t) :
    MonotoneOn h (Set.Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (f' := fun t => (3 * h t ^ 2 + 12 * k t ^ 2) / (4 * Real.pi) ^ 2)
  · intro t ht
    exact (hODE t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hODE t (interior_subset ht)).hasDerivWithinAt
  · intro t _
    positivity
