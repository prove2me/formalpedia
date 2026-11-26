-- Prove2me | solution 2 for MasulloRH.mission_riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T12:04:14.21557+00:00
-- url     : https://prove2.me/submissions/4c8ee43a-bddc-47d8-be2c-9204ee148c7d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_riemannHypothesis_of_cofinal_negative_theta_gram
import Theorems.Thm_MasulloRH_cofinal_theta_gram_negative_direction
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2 := by
  have hRH := MasulloRH.riemannHypothesis_of_cofinal_negative_theta_gram
    MasulloRH.cofinal_theta_gram_negative_direction
  intro s hl hr hz
  exact riemannHypothesis_iff_zeros_in_strip_on_line.mp hRH s hz hl hr
