-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.packet_surjective_monomial_packet_identity_e43f5331
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:06:04.872049+00:00
-- url     : https://prove2.me/submissions/817fbb60-3644-4f90-b9e9-9301fbb85503

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_monomial_coefficient_eq_actualMatrix_e43f5331
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialJet_coeff_sum_e43f5331

open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (a : Column d H → Complex) :
    truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (∑ c : Column d H,
        MvPolynomial.C (a c) *
          MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1) =
    fun rho : Row d H =>
      ∑ c : Column d H, a c * actualMatrix d H rho c := by
  classical
  ext rho
  change
    (truncatedPolynomialJet
      (fun i => (rho.1.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      (∑ c : Column d H,
        MvPolynomial.C (a c) *
          MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1)).coeff
      (InterpolationMatrix.exponentVector rho.2) =
    ∑ c : Column d H, a c * actualMatrix d H rho c
  rw [OAI.PiExponent.DeterminantContradiction.truncatedPolynomialJet_coeff_sum_e43f5331]
  simp_rw [OAI.PiExponent.DeterminantContradiction.packet_monomial_coefficient_eq_actualMatrix_e43f5331]