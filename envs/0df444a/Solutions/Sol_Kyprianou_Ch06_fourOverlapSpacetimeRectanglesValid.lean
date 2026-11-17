-- Prove2me | solution 1 for Kyprianou.Ch06.fourOverlapSpacetimeRectanglesValid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:37:58.750122+00:00
-- url     : https://prove2.me/submissions/c6638320-b319-4d04-a705-a59d3645d31d

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
    (n : Measure E) (B C : Set E)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hFB : n B < ⊤) (hFC : n C < ⊤)
    (s t : NNReal) (hst : s ≤ t) :
    let starts : Fin 4 → NNReal := fun i => if i = 3 then s else 0
    let stops : Fin 4 → NNReal := fun i => if i = 3 then t else s
    let marks : Fin 4 → Set E := fun i =>
      if i = 0 then B \ C else if i = 1 then B ∩ C
        else if i = 2 then C \ B else C
    ∀ i, starts i ≤ stops i ∧
      MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by
  dsimp only
  intro i
  fin_cases i
  · exact ⟨bot_le, hB.diff hC,
      lt_of_le_of_lt (measure_mono Set.diff_subset) hFB⟩
  · exact ⟨bot_le, hB.inter hC,
      lt_of_le_of_lt (measure_mono Set.inter_subset_left) hFB⟩
  · exact ⟨bot_le, hC.diff hB,
      lt_of_le_of_lt (measure_mono Set.diff_subset) hFC⟩
  · exact ⟨hst,hC,hFC⟩
