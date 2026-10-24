-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_packet_canonical_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:28:18.448029+00:00
-- url     : https://prove2.me/submissions/6307f26a-ef49-4b30-9cf4-68d967b4aa53

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_canonical_coefficients_of_positive_weights

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (hw0 : 0 < (d.w0 : Real))
    (hw : ∀ i : Fin d.m,
      0 < MatrixArithmetic.logWeights (finiteDenominators d) i)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) :
    truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      P.val =
    (actualMatrix d H).mulVecLin
      (fun c : Column d H =>
        P.val.coeff (InterpolationMatrix.exponentVector c.1)) := by
  simpa [actualMatrix, Row, Column] using
    (OAI.PiExponent.FormalInterpolation.truncated_packet_canonical_coefficients_of_positive_weights
      d.K d.w0 d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      hw0 hw P)