-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualMatrix_mulVec_coefficients_eq_column_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:36:48.519981+00:00
-- url     : https://prove2.me/submissions/0987c3c4-bb22-4e8f-99df-b2aca200a99d

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (rho : Row d H) :
    (actualMatrix d H).mulVecLin
      (fun c : Column d H => P.1.coeff (InterpolationMatrix.exponentVector c.1)) rho =
    ∑ c : Column d H,
      actualMatrix d H rho c * P.1.coeff (InterpolationMatrix.exponentVector c.1) := by
  classical
  change (∑ c : Column d H,
      actualMatrix d H rho c * P.1.coeff (InterpolationMatrix.exponentVector c.1)) = _
  rfl