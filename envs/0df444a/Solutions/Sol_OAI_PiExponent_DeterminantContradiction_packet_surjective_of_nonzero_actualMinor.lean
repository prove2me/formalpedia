-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.packet_surjective_of_nonzero_actualMinor
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:08:29.908824+00:00
-- url     : https://prove2.me/submissions/8402ddea-3415-4039-a3a6-42979dd6913a

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_selectedMonomialSumRepresentation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_matrixSolutionOfNonzeroDet
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (selection : Row d H → Column d H)
    (hinj : Function.Injective selection)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    Function.Surjective
      (fun P : WeightedPolynomial d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1) := by
  classical
  intro y
  obtain ⟨x, hx⟩ :=
    OAI.PiExponent.DeterminantContradiction.matrixSolutionOfNonzeroDet
      (actualMinor d H selection) hdet y
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.DeterminantContradiction.selectedMonomialSumRepresentation
      nu d H selection hinj x
  refine ⟨P, ?_⟩
  funext rho
  change truncatedPolynomialPacket d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1 rho = y rho
  rw [hP rho]
  exact hx rho