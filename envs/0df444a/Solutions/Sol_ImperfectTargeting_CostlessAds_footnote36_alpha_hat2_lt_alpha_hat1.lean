-- Prove2me | solution 1 for ImperfectTargeting.CostlessAds.footnote36_alpha_hat2_lt_alpha_hat1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:51:21.40478+00:00
-- url     : https://prove2.me/submissions/ac441a19-f530-4dac-b06c-4f0ba2df8851

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting

open MeasureTheory
open ImperfectTargeting.CostlessAds

theorem solution(A : ℝ) (hA0 : 0 < A) (hA : A < 1 / 4) :
    αhat2 A < αhat1 A := by
  unfold αhat2 αhat1
  have hu : 0 < 1 - 4 * A := by linarith
  have hs := Real.sq_sqrt hu.le
  have hs0 := Real.sqrt_nonneg (1 - 4 * A)
  have hne : Real.sqrt (1 - 4 * A) < 1 := by
    rw [Real.sqrt_lt' one_pos]; linarith
  nlinarith [mul_pos (sub_pos.2 hne) (sub_pos.2 hne)]
