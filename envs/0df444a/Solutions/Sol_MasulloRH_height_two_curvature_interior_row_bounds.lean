-- Prove2me | solution 1 for MasulloRH.height_two_curvature_interior_row_bounds
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T14:07:56.008733+00:00
-- url     : https://prove2.me/submissions/cc470ce4-a8aa-48f0-bd9a-d09b5c7af907

import Theorems.Thm_MasulloRH_height_two_curvature_row_of_interval_check
import Theorems.Thm_MasulloRH_height_two_central_interval_checks

open MasulloRH.HeightTwoCurvature Set

theorem solution (j : ℕ) (hL : 144 ≤ j) (hR : j < 960) :
    ∃ A M E : ℝ, 0 ≤ M ∧
      |surrogate j (edge j)| ≤ A ∧ |surrogate j (edge (j+1))| ≤ A ∧
      (∀ x ∈ Icc (edge j) (edge (j+1)),
        |deriv (deriv (surrogate j)) x| ≤ M ∧ tail j x ≤ E) ∧
      Real.exp (3/2 * edge (j+1) + 11/24 * |edge (j+1)|) *
        (A + M/131072 + E)^2 ≤ (cap j : ℝ)/1000000 := by
  apply MasulloRH.height_two_curvature_row_of_interval_check
  have h := List.all_eq_true.mp MasulloRH.height_two_central_interval_checks
    (j-144) (List.mem_range.mpr (by omega))
  simpa only [show 144+(j-144) = j by omega] using h
