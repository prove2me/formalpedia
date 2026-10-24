-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventually_actualPacket_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:43:17.269708+00:00
-- url     : https://prove2.me/submissions/a4c1e53b-a0e3-466d-a175-1d6bd8cea61b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventually_actualMatrix_surjective
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMatrix_surjective_implies_truncatedPacket_surjective
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) :
    ∀ᶠ H : Real in atTop,
      Function.Surjective
        (fun P : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) H =>
          truncatedPolynomialPacket d.K d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) H
            (MatrixArithmetic.rationalCenters (finiteNumerators d)
              (finiteDenominators d))
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
            P.val) := by
  filter_upwards
    [OAI.PiExponent.DeterminantContradiction.eventually_actualMatrix_surjective nu d]
    with H hH
  exact OAI.PiExponent.DeterminantContradiction.actualMatrix_surjective_implies_truncatedPacket_surjective
    nu d H hH