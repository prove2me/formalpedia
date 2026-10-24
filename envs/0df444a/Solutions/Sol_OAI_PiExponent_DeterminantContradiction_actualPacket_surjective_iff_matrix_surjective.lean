-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualPacket_surjective_iff_matrix_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:20:15.074099+00:00
-- url     : https://prove2.me/submissions/0c55dae7-f784-4455-87fd-724b05dde342

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_fixedData_weights_pos
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_packet_canonical_coefficients
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_polynomial_coefficient_map_surjective

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real) :
    Function.Surjective
        (fun P : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
          truncatedPolynomialPacket d.K d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) H
            (MatrixArithmetic.rationalCenters (finiteNumerators d)
              (finiteDenominators d))
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
            P.val) <->
      Function.Surjective (actualMatrix d H).mulVecLin := by
  have hweights :=
    OAI.PiExponent.DeterminantContradiction.fixedData_weights_pos nu d
  have hw0 := hweights.1
  have hw := hweights.2
  constructor
  case mp =>
    intro hPacket y
    cases hPacket y with
    | intro P hP =>
      refine Exists.intro
        (fun c : Column d H =>
          P.val.coeff (InterpolationMatrix.exponentVector c.1)) ?_
      have hcanonical :=
        OAI.PiExponent.DeterminantContradiction.actual_packet_canonical_coefficients
          nu d H hw0 hw P
      change truncatedPolynomialPacket d.K d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) H
          (MatrixArithmetic.rationalCenters (finiteNumerators d)
            (finiteDenominators d))
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
          P.val = y at hP
      calc
        (actualMatrix d H).mulVecLin
            (fun c : Column d H =>
              P.val.coeff (InterpolationMatrix.exponentVector c.1)) =
            truncatedPolynomialPacket d.K d.v0 d.base.theta
              (MatrixArithmetic.logWeights (finiteDenominators d)) H
              (MatrixArithmetic.rationalCenters (finiteNumerators d)
                (finiteDenominators d))
              (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
              P.val := hcanonical.symm
        _ = y := hP
  case mpr =>
    intro hMatrix y
    cases hMatrix y with
    | intro x hx =>
      cases
          (OAI.PiExponent.DeterminantContradiction.polynomial_coefficient_map_surjective
            nu d H x) with
      | intro P hcoeff =>
        refine Exists.intro P ?_
        have hcanonical :=
          OAI.PiExponent.DeterminantContradiction.actual_packet_canonical_coefficients
            nu d H hw0 hw P
        have hvec :
            (fun c : Column d H =>
              P.val.coeff (InterpolationMatrix.exponentVector c.1)) = x := hcoeff
        change truncatedPolynomialPacket d.K d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) H
            (MatrixArithmetic.rationalCenters (finiteNumerators d)
              (finiteDenominators d))
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
            P.val = y
        calc
          truncatedPolynomialPacket d.K d.v0 d.base.theta
              (MatrixArithmetic.logWeights (finiteDenominators d)) H
              (MatrixArithmetic.rationalCenters (finiteNumerators d)
                (finiteDenominators d))
              (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
              P.val =
              (actualMatrix d H).mulVecLin
                (fun c : Column d H =>
                  P.val.coeff (InterpolationMatrix.exponentVector c.1)) := hcanonical
          _ = (actualMatrix d H).mulVecLin x := by rw [hvec]
          _ = y := hx