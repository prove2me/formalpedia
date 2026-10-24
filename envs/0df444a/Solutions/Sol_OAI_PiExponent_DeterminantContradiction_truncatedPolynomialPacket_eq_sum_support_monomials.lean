-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.truncatedPolynomialPacket_eq_sum_support_monomials
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:25:51.107346+00:00
-- url     : https://prove2.me/submissions/9ae040b0-4dbd-4525-a0a2-79b23d365a4b

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
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
    ∑ a ∈ P.1.support,
      FormalInterpolation.truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
        (MvPolynomial.monomial a 1) rho * P.1.coeff a := by
  classical
  simp only [FormalInterpolation.truncatedPolynomialPacket]
  conv_lhs => rw [MvPolynomial.as_sum P.1]
  simp only [map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro a ha
  change
    (FormalInterpolation.truncatedPolynomialJet
      (fun i => (rho.1.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (MvPolynomial.monomial a (P.1.coeff a))).coeff
        (InterpolationMatrix.exponentVector rho.2.val) =
    (FormalInterpolation.truncatedPolynomialJet
      (fun i => (rho.1.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (MvPolynomial.monomial a 1)).coeff
        (InterpolationMatrix.exponentVector rho.2.val) * P.1.coeff a
  rw [show MvPolynomial.monomial a (P.1.coeff a) =
      MvPolynomial.C (P.1.coeff a) * MvPolynomial.monomial a 1 by
    ext b
    simp]
  simp [FormalInterpolation.truncatedPolynomialJet,
    MvPolynomial.coeff_C_mul, mul_comm]