-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_column_sum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:14:24.428605+00:00
-- url     : https://prove2.me/submissions/80e6ca83-b249-4520-98ca-572299e1d422
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_eq_sum_support_monomials
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_monomial_eq_actualMatrix
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_support_sum_eq_column_sum

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

noncomputable section

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H)
    (rho : Row d H) :
    FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1 rho =
    ∑ c : Column d H,
      actualMatrix d H rho c * P.1.coeff (InterpolationMatrix.exponentVector c.1) := by
  rw [OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_sum_support_monomials]
  calc
    (∑ a ∈ P.1.support,
      FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
        (MvPolynomial.monomial a 1) rho * P.1.coeff a) =
      ∑ c : Column d H,
        FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1) rho *
            P.1.coeff (InterpolationMatrix.exponentVector c.1) := by
      exact OAI.PiExponent.DeterminantContradiction.weighted_support_sum_eq_column_sum
        d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H P.1
        (fun a =>
          FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) H
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
            (MvPolynomial.monomial a 1) rho * P.1.coeff a)
        P.2
    _ = ∑ c : Column d H,
        actualMatrix d H rho c * P.1.coeff (InterpolationMatrix.exponentVector c.1) := by
      apply Fintype.sum_congr
      intro c
      rw [OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_monomial_eq_actualMatrix]
