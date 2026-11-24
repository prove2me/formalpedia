-- Prove2me | solution 1 for Kyprianou.Ch03.delayedOpenHitStoppingV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:02:46.109108+00:00
-- url     : https://prove2.me/submissions/4a3e787e-b29f-487a-a9b7-58432a4b1c40
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_stoppingTimeOfStrictSublevelsRCV1
import Theorems.Thm_Kyprianou_Ch03_delayedOpenHitStrictSublevelsV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (hRC : F.IsRightContinuous) (a : NNReal) (U : Set ℝ) (hU : IsOpen U) :
    IsStoppingTime F (fun w => sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ U})) := by
  apply Kyprianou.Ch03.stoppingTimeOfStrictSublevelsRCV1 F hRC
  intro s
  exact Kyprianou.Ch03.delayedOpenHitStrictSublevelsV1 P F X hX hNatural a U hU s
