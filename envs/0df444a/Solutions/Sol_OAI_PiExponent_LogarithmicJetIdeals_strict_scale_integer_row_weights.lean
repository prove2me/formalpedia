-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.strict_scale_integer_row_weights
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T19:23:30.749986+00:00
-- url     : https://prove2.me/submissions/58018066-ce7f-4768-93b1-d676d71a69f9

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_fixed_data_row_weights_pos_rat
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_positive_rational_finite_family_has_integer_common_multiple
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_scale_below_close

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∃ R S : ℝ, 0 < R ∧ R < S ∧
      ∃ e : Fin (d.m + 1) → ℕ, (∀ i, 0 < e i) ∧
        (∀ i, S = (e i : ℝ) *
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
        2 * R ^ (d.m + 1 : ℕ) > S ^ (d.m + 1 : ℕ) := by
  have hrow := OAI.PiExponent.LogarithmicJetIdeals.fixed_data_row_weights_pos_rat d
  obtain ⟨S, hS, e, he, heq⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.positive_rational_finite_family_has_integer_common_multiple
      (fun i => InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
      (fun i => (hrow i).1)
      (fun i => (hrow i).2)
  obtain ⟨R, hR, hRS, hvol⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.strict_scale_below_close
      (d.m + 1) (by omega) S hS
  exact ⟨R, S, hR, hRS, e, he, heq, hvol⟩