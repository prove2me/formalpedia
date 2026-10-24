-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_matrix_mulVec_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:09:37.52584+00:00
-- url     : https://prove2.me/submissions/5c048c03-7341-423d-ad8e-ce759f9e74ea

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_eq_column_sum
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMatrix_mulVec_coefficients_eq_column_sum

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) :
    (actualMatrix d H).mulVecLin
      (fun c : Column d H => P.1.coeff (InterpolationMatrix.exponentVector c.1)) =
    FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1 := by
  funext rho
  rw [OAI.PiExponent.DeterminantContradiction.actualMatrix_mulVec_coefficients_eq_column_sum,
      OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_column_sum]