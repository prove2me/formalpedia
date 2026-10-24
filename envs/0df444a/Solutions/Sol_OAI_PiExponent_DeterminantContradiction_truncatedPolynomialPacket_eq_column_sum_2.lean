-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_column_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:19:52.281569+00:00
-- url     : https://prove2.me/submissions/64cfacba-15a1-4595-8ffd-2d1df1dd4259

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_eq_sum_support_monomials
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_monomial_eq_actualMatrix
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_coefficient_support_sum_eq_column_sum

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
      exact OAI.PiExponent.DeterminantContradiction.weighted_coefficient_support_sum_eq_column_sum
        nu d H P (fun a =>
          FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) H
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
            (MvPolynomial.monomial a 1) rho)
    _ = ∑ c : Column d H,
        actualMatrix d H rho c * P.1.coeff (InterpolationMatrix.exponentVector c.1) := by
      apply Fintype.sum_congr
      intro c
      rw [OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_monomial_eq_actualMatrix]