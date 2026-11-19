-- Prove2me | solution 1 for Kyprianou.Ch03.entranceAndHittingAreStoppingTimes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T14:58:33.265761+00:00
-- url     : https://prove2.me/submissions/e26f786b-bd7d-4c16-9d41-e7f0dd7c57c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_entranceHit_firstEntranceIsStoppingTime
import Theorems.Thm_Kyprianou_Ch03_entranceHit_firstHittingIsStoppingTime
import Theorems.Thm_Kyprianou_Ch03_entranceHit_eventualClosureAtPassage
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real) (hB : IsOpen B ∨ IsClosed B)
    (entranceTime hittingTime : Omega -> NNReal)
    (hEntranceTime : forall omega,
      firstEntranceTime X B omega != ⊤ ->
        firstEntranceTime X B omega = (entranceTime omega : WithTop NNReal))
    (hHittingTime : forall omega,
      firstHittingTime X B omega != ⊤ ->
        firstHittingTime X B omega = (hittingTime omega : WithTop NNReal)) :
    IsStoppingTime F (firstEntranceTime X B) ∧
    IsStoppingTime F (firstHittingTime X B) ∧
    (∀ᵐ omega : Omega ∂ P,
      (firstEntranceTime X B omega != ⊤ ->
        X (entranceTime omega) omega ∈ closure B) ∧
      (firstHittingTime X B omega != ⊤ ->
        X (hittingTime omega) omega ∈ closure B)) := by
  exact ⟨
    Kyprianou.Ch03.entranceHit_firstEntranceIsStoppingTime P F X hX hNatural B hB entranceTime hittingTime hEntranceTime hHittingTime,
    Kyprianou.Ch03.entranceHit_firstHittingIsStoppingTime P F X hX hNatural B hB entranceTime hittingTime hEntranceTime hHittingTime,
    Kyprianou.Ch03.entranceHit_eventualClosureAtPassage P F X hX hNatural B hB entranceTime hittingTime hEntranceTime hHittingTime
  ⟩
