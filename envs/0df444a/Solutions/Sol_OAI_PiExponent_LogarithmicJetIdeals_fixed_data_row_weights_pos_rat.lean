-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.fixed_data_row_weights_pos_rat
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T19:46:26.187962+00:00
-- url     : https://prove2.me/submissions/2bef6553-69fb-4797-b268-4c581aad12d4

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∀ i : Fin (d.m + 1),
      0 < InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i ∧
        ∃ q : ℚ, InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i = (q : ℝ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨d.v0_pos, ⟨d.v0, rfl⟩⟩
  · have hcast :
        ((d.rationalWeight (j.val + 1) : ℚ) : ℝ) =
          MatrixArithmetic.logWeights (finiteDenominators d) j := by
      rw [d.cast_rationalWeight, d.x_log j.val]
      simp [MatrixArithmetic.logWeights, finiteDenominators]
    have hqpos : 0 < (d.rationalWeight (j.val + 1) : ℝ) := by
      exact_mod_cast d.rationalWeight_pos (j.val + 1)
    constructor
    · simpa [InterpolationMatrix.rowWeights, hcast] using
        (div_pos hqpos d.base.theta_pos)
    · refine ⟨d.rationalWeight (j.val + 1) / d.base.theta, ?_⟩
      simpa [InterpolationMatrix.rowWeights, hcast]
