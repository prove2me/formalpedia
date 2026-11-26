-- Prove2me | solution 1 for MasulloRH.height_two_curvature_row_bounds
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T13:33:09.580079+00:00
-- url     : https://prove2.me/submissions/65c90a06-339f-4113-b069-4d70664f87d3

import Theorems.Thm_MasulloRH_height_two_curvature_tail_rows
import Theorems.Thm_MasulloRH_height_two_curvature_interior_row_bounds
import Definitions.Def_MasulloRH_HeightTwoCurvature
import Mathlib.Analysis.Calculus.Deriv.Basic

open MasulloRH.HeightTwoCurvature Set

theorem solution (j : ℕ) (hL : 80 ≤ j) (hR : j < 1008) :
    ∃ A M E : ℝ, 0 ≤ M ∧
      |surrogate j (edge j)| ≤ A ∧ |surrogate j (edge (j+1))| ≤ A ∧
      (∀ x ∈ Icc (edge j) (edge (j+1)),
        |deriv (deriv (surrogate j)) x| ≤ M ∧ tail j x ≤ E) ∧
      Real.exp (3/2 * edge (j+1) + 11/24 * |edge (j+1)|) *
        (A + M/131072 + E)^2 ≤ (cap j : ℝ)/1000000 := by
  by_cases h : j < 144 ∨ 960 ≤ j
  · exact (MasulloRH.height_two_curvature_tail_rows j (by omega) h).1
  · exact MasulloRH.height_two_curvature_interior_row_bounds j (by omega) (by omega)
