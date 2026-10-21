-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:50:29.046854+00:00
-- url     : https://prove2.me/submissions/f5406607-00a6-444d-a193-252703d8a965

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_period_columnFunction_norm_le_of_basic_bound
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_period_column_budget_exponent_le

open scoped BigOperators Topology
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic

theorem solution
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ)
    (w : Fin m → ℝ) {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w0 * (h : ℝ) + ∑ i, w i * (a i : ℝ) ≤ H)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖columnFunction h a A z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  apply le_trans
  · exact OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le_of_basic_bound
      h a A hR hz
  · exact Real.exp_le_exp.mpr
      (OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_column_budget_exponent_le
        h a w hR hH hw0 hws hw hcol)