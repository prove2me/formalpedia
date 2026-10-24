-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.eventually_nonzero_actualMinor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:08:54.790847+00:00
-- url     : https://prove2.me/submissions/7b7a8d44-08a8-4c93-b7de-47f2d755fcdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventually_actualMatrix_surjective
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualMatrix_surjective_gives_nonzero_minor
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution (nu : Real) (d : FixedData nu) :
    ∀ᶠ H : Real in atTop,
      ∃ selection : Row d H → Column d H,
        Function.Injective selection ∧ (actualMinor d H selection).det ≠ 0 := by
  filter_upwards [eventually_actualMatrix_surjective nu d] with H hH
  exact actualMatrix_surjective_gives_nonzero_minor d H hH