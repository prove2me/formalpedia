-- Prove2me | solution 1 for HunterPDE.Newtonian.locallyIntegrable_fundamentalSolution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T21:26:33.816481+00:00
-- url     : https://prove2.me/submissions/bcf550ef-e43a-4637-bd3e-fc951cbf8854

import Definitions.Def_HunterPDE_Newtonian_FundamentalSolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open MeasureTheory
open HunterPDE.Newtonian

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    LocallyIntegrable (fundamentalSolution n) volume := by
  have hd : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa using (show 1 ≤ n by omega)
  by_cases htwo : n = 2
  · have hi : LocallyIntegrable (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖⁻¹) volume := by
      apply locallyIntegrable_of_norm_le_rpow hd (α := 1) (C := 1)
      · simp only [finrank_euclideanSpace, Fintype.card_fin]
        exact_mod_cast (show 1 < n by omega)
      · filter_upwards [] with y
        simp [Real.rpow_neg_one]
      · exact continuous_norm.measurable.inv.aestronglyMeasurable
    have hl : LocallyIntegrable (fun y : EuclideanSpace ℝ (Fin n) => Real.log ‖y‖) volume := by
      apply (continuous_norm.locallyIntegrable.add hi).mono
      · exact continuous_norm.measurable.log.aestronglyMeasurable
      · filter_upwards [] with y
        change |Real.log ‖y‖| ≤ |‖y‖ + ‖y‖⁻¹|
        rw [
          abs_of_nonneg (add_nonneg (norm_nonneg y) (inv_nonneg.mpr (norm_nonneg y)))]
        apply abs_le.mpr
        constructor
        · linarith [Real.neg_inv_le_log (norm_nonneg y), norm_nonneg y]
        · linarith [Real.log_le_self (norm_nonneg y), inv_nonneg.mpr (norm_nonneg y)]
    have hs := hl.smul (-(1 / (2 * Real.pi)))
    change LocallyIntegrable (fun y => -(1 / (2 * Real.pi)) * Real.log ‖y‖) volume at hs
    change LocallyIntegrable (fun y => fundamentalSolution n y) volume
    simpa only [fundamentalSolution, if_pos htwo] using hs
  · have hp : LocallyIntegrable
        (fun y : EuclideanSpace ℝ (Fin n) => 1 / ‖y‖ ^ (n - 2)) volume := by
      apply locallyIntegrable_of_norm_le_rpow hd (α := (n - 2 : ℕ)) (C := 1)
      · simp only [finrank_euclideanSpace, Fintype.card_fin]
        exact_mod_cast (show n - 2 < n by omega)
      · filter_upwards [] with y
        simp [Real.rpow_neg_natCast, zpow_neg]
      · have hm : Measurable (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ (n - 2)) :=
          continuous_norm.measurable.pow_const (n - 2)
        simpa only [one_div, Pi.inv_def] using hm.inv.aestronglyMeasurable
    have hs := hp.smul (1 / ((n : ℝ) * ((n : ℝ) - 2) * unitBallVolume n))
    change LocallyIntegrable (fun y =>
      (1 / ((n : ℝ) * ((n : ℝ) - 2) * unitBallVolume n)) * (1 / ‖y‖ ^ (n - 2))) volume at hs
    change LocallyIntegrable (fun y => fundamentalSolution n y) volume
    simpa only [fundamentalSolution, if_neg htwo] using hs
