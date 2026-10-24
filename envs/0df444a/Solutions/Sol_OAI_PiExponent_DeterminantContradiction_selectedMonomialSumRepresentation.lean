-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.selectedMonomialSumRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:12:29.300804+00:00
-- url     : https://prove2.me/submissions/cf6a3484-9cc3-49c4-ad83-73aba9d15f68

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_selectedMonomialSumPolynomial
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_selectedMonomialSumPacket
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

 theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (selection : Row d H → Column d H)
    (hinj : Function.Injective selection)
    (x : Row d H → Complex) :
    ∃ P : WeightedPolynomial d.w0
        (MatrixArithmetic.logWeights (finiteDenominators d)) H,
      ∀ rho : Row d H,
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1 rho =
          ∑ sigma : Row d H, (actualMinor d H selection) rho sigma * x sigma := by
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.DeterminantContradiction.selectedMonomialSumPolynomial
      nu d H selection x
  refine ⟨P, ?_⟩
  intro rho
  rw [hP]
  exact OAI.PiExponent.DeterminantContradiction.selectedMonomialSumPacket
    nu d H selection x rho