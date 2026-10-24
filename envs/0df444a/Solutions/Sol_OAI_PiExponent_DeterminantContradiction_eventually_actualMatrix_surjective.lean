-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventually_actualMatrix_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:51:48.302184+00:00
-- url     : https://prove2.me/submissions/4bd0651b-66b6-4ac9-91d7-f45ecdc61365
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventually_truncatedPolynomialPacket_surjective
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialPacket_surjective_implies_matrix_surjective

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) :
    ∀ᶠ H : Real in atTop,
      Function.Surjective (actualMatrix d H).mulVecLin := by
  filter_upwards
    [eventually_truncatedPolynomialPacket_surjective nu d] with H hH
  exact truncatedPolynomialPacket_surjective_implies_matrix_surjective nu d H hH