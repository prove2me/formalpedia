-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.strict_scale_padded_packet_interpolation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T22:37:30.474076+00:00
-- url     : https://prove2.me/submissions/b4bc0d01-9450-406a-bf37-9db33ce94cb9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_scale_integer_row_weights
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_bounded_raw_packet_interpolation

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
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          Function.Surjective
            (fun Q : WeightedPolynomial d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * R) =>
              rawPacketMap d.K d.v0 d.base.theta
                (MatrixArithmetic.logWeights (finiteDenominators d))
                (((n + d.m : ℕ) : ℝ) * S)
                (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
                Q.val) := by
  obtain ⟨R, S, hR, hRS, e, he, hcommon, hcapacity⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.strict_scale_integer_row_weights d
  obtain ⟨N, hN⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.eventual_bounded_raw_packet_interpolation
      d R S e hR hRS he hcommon hcapacity
  exact ⟨R, S, hR, hRS, e, he, hcommon, N, hN⟩