-- Prove2me | solution 1 for Kyprianou.Ch06.fourOverlapSpacetimeMarksDisjointFromA
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:38:05.425287+00:00
-- url     : https://prove2.me/submissions/222e2221-22c9-44c8-96af-47ab1a7c4734

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {E : Type} [MeasurableSpace E]
    (A B C : Set E)
    (hAB : Disjoint A B) (hAC : Disjoint A C) :
    let marks : Fin 4 → Set E := fun i =>
      if i = 0 then B \ C else if i = 1 then B ∩ C
        else if i = 2 then C \ B else C
    ∀ i, Disjoint A (marks i) := by
  dsimp only
  intro i
  fin_cases i
  · exact hAB.mono_right Set.diff_subset
  · exact hAB.mono_right Set.inter_subset_left
  · exact hAC.mono_right Set.diff_subset
  · exact hAC
