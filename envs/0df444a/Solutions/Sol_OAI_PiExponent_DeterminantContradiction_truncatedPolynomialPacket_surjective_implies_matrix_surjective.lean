-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_surjective_implies_matrix_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:04:50.716124+00:00
-- url     : https://prove2.me/submissions/1519b82f-a30c-415a-8547-555d74c521a6

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_eq_matrix_mulVec_coefficients

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (hpacket : Function.Surjective
      (fun P : FormalInterpolation.WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1)) :
    Function.Surjective (actualMatrix d H).mulVecLin := by
  classical
  intro f
  obtain ⟨P, hP⟩ := hpacket f
  refine ⟨fun c : Column d H => P.1.coeff (InterpolationMatrix.exponentVector c.1), ?_⟩
  calc
    (actualMatrix d H).mulVecLin
        (fun c : Column d H => P.1.coeff (InterpolationMatrix.exponentVector c.1)) =
      FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1 :=
          OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_matrix_mulVec_coefficients
            nu d H P
    _ = f := hP