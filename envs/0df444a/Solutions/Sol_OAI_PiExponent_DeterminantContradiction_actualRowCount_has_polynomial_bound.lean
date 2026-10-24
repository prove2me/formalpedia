-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_has_polynomial_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:04:15.344984+00:00
-- url     : https://prove2.me/submissions/5177706b-68c3-4d53-9957-9064744fca98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_polynomial_upper_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_positive
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    ∃ C : Real, 0 < C ∧ ∀ᶠ H : Real in atTop,
      0 < (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ∧
        (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ≤
          C * (H + 1) ^ (d.m + 1) := by
  obtain ⟨C, hC, hUpper⟩ :=
    OAI.PiExponent.DeterminantContradiction.actualRowCount_polynomial_upper_bound d
  refine ⟨C, hC, ?_⟩
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun H hH => hH⟩] with H hH
  exact ⟨OAI.PiExponent.DeterminantContradiction.actualRowCount_positive d
      (lt_of_lt_of_le zero_lt_one hH), hUpper H hH⟩