-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.packet_monomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:18.808636+00:00
-- url     : https://prove2.me/submissions/c7c1b839-cd17-4738-b296-691fdaabd6b2

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_monomial_packet_identity_e43f5331
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
          MvPolynomial.monomial
            (InterpolationMatrix.exponentVector c.1) 1) =
      fun rho : Row d H =>
        ∑ c : Column d H, a c * actualMatrix d H rho c := by
  apply OAI.PiExponent.DeterminantContradiction.packet_surjective_monomial_packet_identity_e43f5331 <;> assumption
