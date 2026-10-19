-- Prove2me | solution 2 for OAI.PiExponent.AdmissibleFormalInterpolation.eventual_scaled_packets
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T21:48:03.149648+00:00
-- url     : https://prove2.me/submissions/1325af10-1b40-4357-ae98-6b3115021c61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_padded_raw_packet_surjective
import Mathlib.Tactic
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution (nu : ℝ) (hnu : 2 < nu) (d : FixedData nu) :
    ∃ R : ℚ, 0 < R ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Surjective (packetMap d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))) := by
  let R : ℚ := 1
  have hR : 0 < R := by norm_num [R]
  obtain ⟨N, hN⟩ :=
    LogarithmicJetIdeals.eventual_padded_raw_packet_surjective d R hR 0
  refine ⟨R, hR, N, ?_⟩
  intro n hn
  change Function.Surjective
    (fun Q : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ)) =>
      LogarithmicJetIdeals.rawPacketMap d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d))
        ((n : ℝ) * (R : ℝ))
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        Q.val)
  simpa only [Nat.add_zero] using hN n hn
