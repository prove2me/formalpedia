-- Prove2me | solution 1 for Kyprianou.Ch03.entranceHit_firstHittingIsStoppingTime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T03:35:24.904034+00:00
-- url     : https://prove2.me/submissions/f8feecf2-5656-405d-b4d5-5ba82ffea8b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_entranceHit_firstHittingIsStoppingTime_of_isOpen
import Theorems.Thm_Kyprianou_Ch03_entranceHit_firstHittingIsStoppingTime_of_isClosed

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Sketch for Theorem 3.3 (hitting clause): case-split on `IsOpen B ∨ IsClosed B`.
Both children retain the finite-time witnesses and completed-natural-filtration hypotheses.
-/

open Kyprianou.Ch03 in
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
    IsStoppingTime F (firstHittingTime X B) := by
  cases hB with
  | inl hOpen =>
      exact entranceHit_firstHittingIsStoppingTime_of_isOpen
        P F X hX hNatural B hOpen entranceTime hittingTime hEntranceTime hHittingTime
  | inr hClosed =>
      exact entranceHit_firstHittingIsStoppingTime_of_isClosed
        P F X hX hNatural B hClosed entranceTime hittingTime hEntranceTime hHittingTime
