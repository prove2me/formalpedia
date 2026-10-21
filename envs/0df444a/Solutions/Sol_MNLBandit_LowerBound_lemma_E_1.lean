-- Prove2me | solution 1 for MNLBandit.LowerBound.lemma_E_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:33:36.917013+00:00
-- url     : https://prove2.me/submissions/133843e9-bdc4-410e-9657-b1d14c704e8e

import Mathlib
import Definitions.Def_RegretBandits_Stochastic_klBernoulli

set_option autoImplicit false

theorem solution (α ϵ : ℝ) (hα : 0 < α) (hϵ : 0 < ϵ) (hαϵ : α + ϵ ≤ 3 / 4) :
    RegretBandits.Stochastic.klBern α (α + ϵ) ≤ 4 / α * ϵ ^ 2 := by
  unfold RegretBandits.Stochastic.klBern
  have hq : 0 < α + ϵ := by linarith
  have hp1 : 0 < 1 - α := by linarith
  have hq1 : 0 < 1 - (α + ϵ) := by linarith
  have h1 : Real.log (α / (α + ϵ)) ≤ α / (α + ϵ) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hα hq)
  have h2 : Real.log ((1 - α) / (1 - (α + ϵ))) ≤ (1 - α) / (1 - (α + ϵ)) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hp1 hq1)
  have h3 := mul_le_mul_of_nonneg_left h1 hα.le
  have h4 := mul_le_mul_of_nonneg_left h2 hp1.le
  have key : α * (α / (α + ϵ) - 1) + (1 - α) * ((1 - α) / (1 - (α + ϵ)) - 1)
      = ϵ ^ 2 / ((α + ϵ) * (1 - (α + ϵ))) := by
    field_simp
    ring
  have hden : α / 4 ≤ (α + ϵ) * (1 - (α + ϵ)) := by nlinarith
  have h5 : ϵ ^ 2 / ((α + ϵ) * (1 - (α + ϵ))) ≤ ϵ ^ 2 / (α / 4) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have h6 : ϵ ^ 2 / (α / 4) = 4 / α * ϵ ^ 2 := by field_simp
  linarith
