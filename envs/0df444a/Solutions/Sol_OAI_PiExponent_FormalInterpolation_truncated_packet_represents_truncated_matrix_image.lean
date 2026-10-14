-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.truncated_packet_represents_truncated_matrix_image
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T08:09:24.926298+00:00
-- url     : https://prove2.me/submissions/13c5fbec-4575-424d-b7c1-32d5d0082554
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_polynomial_realizes_column_coefficients_for_truncated_image
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_truncated_packet_matrix_of_polynomial_coefficients

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (T : Fin d.m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (x : InterpolationMatrix.Column d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H → Complex) :
    ∃ P : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T P.val =
      (InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T).mulVecLin x := by
  obtain ⟨P, hcoeff⟩ :=
    OAI.PiExponent.FormalInterpolation.weighted_polynomial_realizes_column_coefficients_for_truncated_image
      d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H x
  refine ⟨P, ?_⟩
  rw [OAI.PiExponent.FormalInterpolation.truncated_packet_matrix_of_polynomial_coefficients]
  have hfun : (fun c : InterpolationMatrix.Column d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        P.val.coeff (InterpolationMatrix.exponentVector c.1)) = x := by
    funext c
    exact hcoeff c
  rw [hfun]
