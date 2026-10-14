-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.packetMap_factors_through_truncated_matrix
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T07:11:58.968386+00:00
-- url     : https://prove2.me/submissions/7d1632a8-d453-4a44-95bf-331e4cd79013
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_formal_packet_eq_truncated_packet_of_row_bound
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_represents_truncated_matrix_image
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (T : Fin d.m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0) :
    ∀ x : InterpolationMatrix.Column d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H → Complex,
      ∃ P : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) H,
        packetMap d H P =
          (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) H
            (MatrixArithmetic.rationalCenters (finiteNumerators d)
              (finiteDenominators d)) T).mulVecLin x := by
  intro x
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.FormalInterpolation.truncated_packet_represents_truncated_matrix_image
      nu d H T hT x
  refine ⟨P, ?_⟩
  rw [OAI.PiExponent.FormalInterpolation.formal_packet_eq_truncated_packet_of_row_bound
    nu d H T hT P]
  exact hP
