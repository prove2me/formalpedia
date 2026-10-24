-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.arbitrarily_large_nonzero_fixed_minor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:03:35.027928+00:00
-- url     : https://prove2.me/submissions/98db2929-3775-4971-b381-49fae76bad4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_cofinal_actualMatrix_surjective
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_surjective_actualMatrix_has_nonzero_minor
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (L : Real) :
    ∃ H : Real, L ≤ H ∧ 0 < H ∧ 0 < actualRowCount d H ∧
      ∃ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 := by
  obtain ⟨H, hmaxH, hH, hsurj⟩ :=
    OAI.PiExponent.DeterminantContradiction.cofinal_actualMatrix_surjective
      nu d (max L 1)
  obtain ⟨hcount, selection, hdet⟩ :=
    OAI.PiExponent.DeterminantContradiction.surjective_actualMatrix_has_nonzero_minor
      nu d H hH hsurj
  refine ⟨H, le_trans (le_max_left L 1) hmaxH, hH, hcount, selection, hdet⟩