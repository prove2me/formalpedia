-- Prove2me | solution 1 for Kyprianou.Ch03.entranceHit_firstHittingIsStoppingTime_of_isClosed
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T10:49:47.932106+00:00
-- url     : https://prove2.me/submissions/7b1ef2db-77c4-425f-ae44-c0e74a5478fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch03_completedStoppingInfSupAEEqV1
import Theorems.Thm_Kyprianou_Ch03_closedHitApproximationAELimitV1
import Theorems.Thm_Kyprianou_Ch03_openHitAfterCutoffStoppingV1
import Theorems.Thm_Kyprianou_Ch03_completedNaturalLevyFiltrationRightContinuous
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
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
  let U (m n : ℕ) (w : Omega) := sInf {u : WithTop NNReal | ∃ r : NNReal,
    (1 / ((m : NNReal) + 1)) < r ∧
    X r w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B ∧ u = (r : WithTop NNReal)}
  have hRC := completedNaturalLevyFiltrationRightContinuous P X hX F hNatural
  have hU (m n : ℕ) : IsStoppingTime F (U m n) :=
    openHitAfterCutoffStoppingV1 P F X hX hNatural
      (Metric.thickening (1 / ((n : ℝ) + 1)) B) Metric.isOpen_thickening
      (1 / ((m : NNReal) + 1)) hRC
  have he := closedHitApproximationAELimitV1 P F X hX hNatural B hB hU
  exact completedStoppingInfSupAEEqV1 P F X hX hNatural
    (firstHittingTime X B) U hRC hU he
