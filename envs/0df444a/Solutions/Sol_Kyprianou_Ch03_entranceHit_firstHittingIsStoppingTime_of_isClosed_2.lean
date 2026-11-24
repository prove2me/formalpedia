-- Prove2me | solution 2 for Kyprianou.Ch03.entranceHit_firstHittingIsStoppingTime_of_isClosed
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T10:49:57.07644+00:00
-- url     : https://prove2.me/submissions/6bc5cf63-4253-4cde-a71d-eb0f59685b7e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_completedNaturalLevyFiltrationRightContinuous
import Theorems.Thm_Kyprianou_Ch03_delayedOpenHitStoppingV1
import Theorems.Thm_Kyprianou_Ch03_closedHitDelayedApproxAEEqV1
import Theorems.Thm_Kyprianou_Ch03_completedStoppingTimeIInfISupAEEqV1
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
    (B : Set Real)
    (hB : IsClosed B)
    (entranceTime hittingTime : Omega -> NNReal)
    (hEntranceTime : forall omega,
      firstEntranceTime X B omega != ⊤ ->
        firstEntranceTime X B omega = (entranceTime omega : WithTop NNReal))
    (hHittingTime : forall omega,
      firstHittingTime X B omega != ⊤ ->
        firstHittingTime X B omega = (hittingTime omega : WithTop NNReal)) :
    IsStoppingTime F (firstHittingTime X B) := by
  have hRC := completedNaturalLevyFiltrationRightContinuous P X hX F hNatural
  let T : ℕ → ℕ → Omega → WithTop NNReal := fun j n w =>
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 1 / ((j : NNReal) + 1) ≤ t ∧
        X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B})
  have hT (j n : ℕ) : IsStoppingTime F (T j n) :=
    delayedOpenHitStoppingV1 P F X hX hNatural hRC _ _ Metric.isOpen_thickening
  exact completedStoppingTimeIInfISupAEEqV1 P F X hX hNatural hRC T hT _
    (closedHitDelayedApproxAEEqV1 P F X hX hNatural B hB hT)
