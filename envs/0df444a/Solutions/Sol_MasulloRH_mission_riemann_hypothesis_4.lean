-- Prove2me | solution 4 for MasulloRH.mission_riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:31:24.071627+00:00
-- url     : https://prove2.me/submissions/1ace2f3a-72ac-4a5f-829a-893fa49eba95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_riemann_hypothesis_of_unbounded_factorial_gram_tests
import Theorems.Thm_MasulloRH_factorial_gram_negative_direction_from_tolerance_16666
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  have h := riemannHypothesis_iff_zeros_in_strip_on_line.1
    (MasulloRH.riemann_hypothesis_of_unbounded_factorial_gram_tests
      MasulloRH.factorial_gram_negative_direction_from_tolerance_16666)
  intro s hl hr hz
  exact h s hz hl hr
