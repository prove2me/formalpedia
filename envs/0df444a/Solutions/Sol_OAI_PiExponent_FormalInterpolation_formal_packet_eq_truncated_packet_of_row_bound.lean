-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.formal_packet_eq_truncated_packet_of_row_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T07:15:25.460742+00:00
-- url     : https://prove2.me/submissions/ef0ed393-3d9f-4276-97b9-f5f9aa293ef4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_formal_coeff_eq_truncated_coeff_of_row_bound

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (T : Fin d.m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) :
    packetMap d H P =
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T P.val := by
  funext rho
  exact OAI.PiExponent.FormalInterpolation.formal_coeff_eq_truncated_coeff_of_row_bound
    d.K d.w0 d.v0 d.base.theta (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T
    hT P rho
