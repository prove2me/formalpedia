-- Prove2me | solution 1 for ImperfectTargeting.CostlessAds.threshold_alpha_hat2_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:15:24.858895+00:00
-- url     : https://prove2.me/submissions/17d7aa49-c9f4-42fd-8d77-6176e8a5e269

import Mathlib
import Definitions.Def_ImperfectTargeting_CostlessAds_PricingGame
import Definitions.Def_ImperfectTargeting_CostlessAds_Setting
set_option autoImplicit false
open MeasureTheory
open ImperfectTargeting.CostlessAds

theorem solution (A α : ℝ) (hA0 : 0 < A) (hA : A ≤ 1 / 4)
    (hα : 1 / 2 < α) (hα1 : α ≤ 1) :
    A ≤ α * (1 - α) ↔ α ≤ αhat2 A := by
  unfold αhat2
  have h0 : 0 ≤ 1 - 4 * A := by linarith
  have hs := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg (1 - 4 * A)
  constructor
  · intro h
    have : 2 * α - 1 ≤ Real.sqrt (1 - 4 * A) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    linarith
  · intro h
    have h2 : 2 * α - 1 ≤ Real.sqrt (1 - 4 * A) := by linarith
    have h3 : (2 * α - 1) ^ 2 ≤ (Real.sqrt (1 - 4 * A)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h2 2
    nlinarith
