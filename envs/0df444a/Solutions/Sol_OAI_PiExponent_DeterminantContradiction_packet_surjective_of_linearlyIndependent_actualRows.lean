-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.packet_surjective_of_linearlyIndependent_actualRows
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:41:08.464894+00:00
-- url     : https://prove2.me/submissions/bf525375-06f4-4acc-a2f2-97397a4e73cb

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_actualRows_coefficients_e43f5331
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_weighted_monomial_sum_e43f5331
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_monomial_packet_identity_e43f5331

open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (hrows : LinearIndependent Complex (fun rho : Row d H => actualMatrix d H rho)) :
    Function.Surjective
      (fun P : WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
        truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d)
            (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
          P.1) := by
  classical
  intro values
  obtain ⟨a, ha⟩ :=
    OAI.PiExponent.DeterminantContradiction.packet_surjective_actualRows_coefficients_e43f5331
      nu d H hrows values
  obtain ⟨P, hP⟩ :=
    OAI.PiExponent.DeterminantContradiction.packet_surjective_weighted_monomial_sum_e43f5331
      nu d H a
  refine ⟨P, ?_⟩
  funext rho
  change truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d)
        (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
      P.1 rho = values rho
  rw [hP]
  rw [OAI.PiExponent.DeterminantContradiction.packet_surjective_monomial_packet_identity_e43f5331]
  exact ha rho