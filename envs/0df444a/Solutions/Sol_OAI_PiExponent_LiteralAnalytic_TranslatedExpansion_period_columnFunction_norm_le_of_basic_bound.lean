-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le_of_basic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T08:59:13.590117+00:00
-- url     : https://prove2.me/submissions/a4208a0a-7abe-4a07-a668-c6dbe9b843ce

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_period_columnFunction_norm_le_of_factorized_bound

open scoped BigOperators Topology

theorem solution
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ)
    {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.columnFunction h a A z‖ ≤
      Real.exp ((h : ℝ) * R + (∑ i, (a i : ℝ)) * Real.log (2 * R)) := by
  have hfactor := OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le_of_factorized_bound
    h a A hR hz
  rw [Real.exp_add]
  exact hfactor