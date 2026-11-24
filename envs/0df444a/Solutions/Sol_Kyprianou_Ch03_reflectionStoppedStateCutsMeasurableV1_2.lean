-- Prove2me | solution 2 for Kyprianou.Ch03.reflectionStoppedStateCutsMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:50:06.321661+00:00
-- url     : https://prove2.me/submissions/4aac950e-ea94-46cf-b6bf-64613df92d68

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_reflectionSignedAdaptedRightAEV1
import Theorems.Thm_Kyprianou_Ch03_reflectionStoppedCutOfAdaptedRightAEV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
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
  obtain ⟨hAdapt,hRight⟩ := reflectionSignedAdaptedRightAEV1 P X hX F hNatural c y
  exact reflectionStoppedCutOfAdaptedRightAEV1 P X F hNatural _ hAdapt hRight
    tau hTau finiteTime hFinite
