-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_monomial_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:20.003983+00:00
-- url     : https://prove2.me/submissions/e14769fc-be4d-4b57-b589-6369cebd2bd6

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_weighted_monomial_sum_e43f5331
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (a : Column d H → Complex) :
    ∃ P : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      P.1 =
        ∑ c : Column d H,
          MvPolynomial.C (a c) *
            MvPolynomial.monomial
              (InterpolationMatrix.exponentVector c.1) 1 := by
  apply OAI.PiExponent.DeterminantContradiction.packet_surjective_weighted_monomial_sum_e43f5331 <;> assumption
