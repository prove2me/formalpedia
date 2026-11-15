-- Prove2me | solution 1 for InfoLossLAR.WorstCase.fixed_family_approximation_bound
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:30:39.283204+00:00
-- url     : https://prove2.me/submissions/c5807847-b129-4b30-885c-b481e26aa602

import Definitions.Def_InfoLossLAR_WorstCase_Family

set_option autoImplicit false
open InfoLossLAR.WorstCase

theorem solution (lam : ℕ) :
    (famN lam : ℝ) * (famq lam : ℝ) / (famσ lam : ℝ) ≤ famq lam := by
  have hσ : (0 : ℝ) < (famσ lam : ℝ) := by unfold famσ famL; positivity
  have hNσ : (famN lam : ℝ) ≤ (famσ lam : ℝ) := by simp [famN, famσ, famL]
  apply (div_le_iff₀ hσ).2
  exact mul_le_mul_of_nonneg_right hNσ (by positivity) |>.trans_eq (mul_comm _ _)
