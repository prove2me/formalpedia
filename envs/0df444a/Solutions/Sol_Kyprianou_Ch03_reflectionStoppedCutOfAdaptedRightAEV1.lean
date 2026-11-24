-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionStoppedCutOfAdaptedRightAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:01:22.960971+00:00
-- url     : https://prove2.me/submissions/008337ff-73c9-4a9a-a824-d9f35420283f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_Kyprianou_Ch03_completedNaturalStoppedAdaptedEventsV1
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (R : NNReal → Omega → ℝ)
    (hAdapt : ∀ s : NNReal, Measurable[F s] (R s))
    (hRight : ∀ᵐ w ∂P, ∀ s : NNReal,
      ContinuousWithinAt (fun u => R u w) (Set.Ici s) s)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal)) :
    ∀ B : Set ℝ, MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s] ({w | R (finiteTime w) w ∈ B}
        ∩ {w | tau w ≤ (s : WithTop NNReal)}) := by
  have h := completedNaturalStoppedAdaptedEventsV1 P X F hNatural R hAdapt hRight
    tau hTau finiteTime hFinite Set.univ (fun s => by simpa using hTau s)
  intro B hB s
  simpa using h.2 B hB s
