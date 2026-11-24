-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionStoppedStateCutsMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:38:34.791899+00:00
-- url     : https://prove2.me/submissions/f9ec04c3-a787-4d8e-8b3a-8f3a4df775d5

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_Kyprianou_Ch03_completedNaturalStoppedAdaptedEventsV1
import Theorems.Thm_Kyprianou_Ch03_reflectedSignedAdaptedV1
import Theorems.Thm_Kyprianou_Ch03_reflectedSignedRightContinuousAEV1
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (c y : ℝ) :
    ∀ B : Set ℝ, MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s]
        ({w | reflectedSup (fun u v => c * X u v) y (finiteTime w) w ∈ B}
          ∩ {w | tau w ≤ (s : WithTop NNReal)}) := by
  have h := completedNaturalStoppedAdaptedEventsV1 P X F hNatural
    (reflectedSup (fun u v => c * X u v) y)
    (reflectedSignedAdaptedV1 P X hX c y F hNatural)
    (reflectedSignedRightContinuousAEV1 P X hX c y)
    tau hTau finiteTime hFinite Set.univ (fun s => by simpa using hTau s)
  intro B hB s
  simpa using h.2 B hB s
