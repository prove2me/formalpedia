-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionSignedAdaptedRightAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:01:29.643454+00:00
-- url     : https://prove2.me/submissions/2ec16506-9765-48a3-b1e0-2742ac18bd5e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
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
    (c y : ℝ) :
    (∀ s : NNReal, Measurable[F s] (reflectedSup (fun u v => c * X u v) y s)) ∧
    (∀ᵐ w ∂P, ∀ s : NNReal,
      ContinuousWithinAt (fun u => reflectedSup (fun v z => c * X v z) y u w) (Set.Ici s) s) := by
  exact ⟨reflectedSignedAdaptedV1 P X hX c y F hNatural,
    reflectedSignedRightContinuousAEV1 P X hX c y⟩
