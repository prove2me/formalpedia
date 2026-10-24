-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventually_truncatedPolynomialPacket_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:56:55.39684+00:00
-- url     : https://prove2.me/submissions/a0a252bb-0c35-4d68-be54-4d3d4a5faa66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventually_nonzero_actualMinor
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_packet_surjective_of_nonzero_actualMinor
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution (nu : Real) (d : FixedData nu) :
    ∀ᶠ H : Real in atTop,
      Function.Surjective
        (fun P : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
          truncatedPolynomialPacket d.K d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) H
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0) P.1) := by
  filter_upwards [eventually_nonzero_actualMinor nu d] with H hH
  rcases hH with ⟨selection, hinj, hdet⟩
  exact packet_surjective_of_nonzero_actualMinor nu d H selection hinj hdet