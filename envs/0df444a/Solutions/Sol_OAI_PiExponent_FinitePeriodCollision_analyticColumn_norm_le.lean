-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.analyticColumn_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T07:52:47.976921+00:00
-- url     : https://prove2.me/submissions/951ca404-da20-432d-9642-ab0776ec9015

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_factor_bound
import Theorems.Thm_OAI_PiExponent_FinitePeriodCollision_analyticColumn_budget_exponent

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

theorem solution
    {m : ℕ} (h : ℕ) (a A : Fin m → ℕ) (w : Fin m → ℝ)
    {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * (h : ℝ) + ∑ i, w i * (a i : ℝ) ≤ H)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖analyticColumn h a A z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  apply le_trans (analyticColumn_factor_bound h a A w hR hws hw hz)
  exact analyticColumn_budget_exponent h a w hR hH hw0 hws hw hcol