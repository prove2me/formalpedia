-- Prove2me | solution 1 for Kyprianou.Ch03.entranceHit_firstHittingIsStoppingTime_of_isOpen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T03:42:36.859193+00:00
-- url     : https://prove2.me/submissions/9e45f45d-ecdf-4628-aea4-24319984d8fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_completedNaturalLevyFiltrationRightContinuous
import Theorems.Thm_Kyprianou_Ch03_entranceHit_firstHittingIsStoppingTime_of_isOpen_of_rightCont

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Open-hitting stopping time (Thm 3.3 clause): factor Exercise 3.1 right continuity,
then apply the open-debut core under an explicit `F.IsRightContinuous` hypothesis.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real)
    (hB : IsOpen B)
    (entranceTime hittingTime : Omega -> NNReal)
    (hEntranceTime : forall omega,
      firstEntranceTime X B omega != ⊤ ->
        firstEntranceTime X B omega = (entranceTime omega : WithTop NNReal))
    (hHittingTime : forall omega,
      firstHittingTime X B omega != ⊤ ->
        firstHittingTime X B omega = (hittingTime omega : WithTop NNReal)) :
    IsStoppingTime F (firstHittingTime X B) := by
  have hRC : F.IsRightContinuous :=
    completedNaturalLevyFiltrationRightContinuous P X hX F hNatural
  exact entranceHit_firstHittingIsStoppingTime_of_isOpen_of_rightCont
    P F X hX hNatural B hB hRC entranceTime hittingTime hEntranceTime hHittingTime
