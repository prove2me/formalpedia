-- Prove2me | solution 5 for MasulloRH.mission_riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T00:18:47.734273+00:00
-- url     : https://prove2.me/submissions/9665d712-c7f8-431b-a1e2-c23d601fe285
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_riemann_hypothesis_of_unbounded_factorial_gram_tests
import Theorems.Thm_MasulloRH_factorial_grid_four_passes_first_32_billion_gaussian_tests
import Theorems.Thm_MasulloRH_factorial_gram_negative_direction_from_32_billion
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  have h := riemannHypothesis_iff_zeros_in_strip_on_line.1
    (MasulloRH.riemann_hypothesis_of_unbounded_factorial_gram_tests
      (fun j _ => by
      by_cases h : j < 32000000000
      · exact ⟨4,MasulloRH.factorial_grid_four_passes_first_32_billion_gaussian_tests j h⟩
      · exact MasulloRH.factorial_gram_negative_direction_from_32_billion j (by omega)))
  intro s hl hr hz
  exact h s hz hl hr
