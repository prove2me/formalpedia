-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.packet_matrix_surjectivity_gives_right_inverse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T07:06:21.512628+00:00
-- url     : https://prove2.me/submissions/ea6aee1b-d1b7-4de3-bccf-99620000a9ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_packetMap_factors_through_truncated_matrix

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (T : Fin d.m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hmat : Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        T).mulVecLin) :
    ∃ F : (Row d H → Complex) →
        WeightedPolynomial d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      ∀ y : Row d H → Complex, packetMap d H (F y) = y := by
  classical
  let A := InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T
  refine ⟨fun y => Classical.choose
    (OAI.PiExponent.FormalInterpolation.packetMap_factors_through_truncated_matrix
      nu d H T hT (Classical.choose (hmat y))), ?_⟩
  intro y
  have hxy : A.mulVecLin (Classical.choose (hmat y)) = y := Classical.choose_spec (hmat y)
  have hp := Classical.choose_spec
    (OAI.PiExponent.FormalInterpolation.packetMap_factors_through_truncated_matrix
      nu d H T hT (Classical.choose (hmat y)))
  change packetMap d H (Classical.choose
      (OAI.PiExponent.FormalInterpolation.packetMap_factors_through_truncated_matrix
        nu d H T hT (Classical.choose (hmat y)))) = y
  rw [hp]
  simpa [A] using hxy
