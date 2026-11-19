-- Prove2me | solution 1 for LevyStochCalc.Poisson.pairwiseDisjoint_timeSlab
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:59:29.228266+00:00
-- url     : https://prove2.me/submissions/ea74b987-902a-496f-bd1d-bfb9957f3b3e

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000

open LevyStochCalc.Poisson

theorem solution (n : ℕ) :
    Pairwise (Function.onFun Disjoint (timeSlab n)) := by
  have hle : ∀ i j : ℕ, i < j → Disjoint (timeSlab n i) (timeSlab n j) := by
    intro i j hij
    rw [timeSlab, timeSlab, Set.disjoint_left]
    intro x hxi hxj
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have hij1 : ((i : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast hij
    have hdiv : ((i : ℝ) + 1) / 2 ^ n ≤ (j : ℝ) / 2 ^ n :=
      div_le_div_of_nonneg_right hij1 h2pos.le
    linarith [hxi.2, hxj.1]
  intro i j hij
  rcases lt_trichotomy i j with h | rfl | h
  · exact hle i j h
  · exact absurd rfl hij
  · exact (hle j i h).symm
