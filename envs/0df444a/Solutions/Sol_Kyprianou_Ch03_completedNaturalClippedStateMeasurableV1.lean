-- Prove2me | solution 1 for Kyprianou.Ch03.completedNaturalClippedStateMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:13:37.445293+00:00
-- url     : https://prove2.me/submissions/f0ce88ac-b788-49bf-a412-5c6ba42249f5

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_boundedStoppingUpperGridV1
import Theorems.Thm_Kyprianou_Ch03_completedNaturalMeasurableAELimitV1
import Theorems.Thm_Kyprianou_Ch03_boundedCountableStoppedStateMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (Z : NNReal → Omega → ℝ) (hAdapt : Adapted F Z)
    (hRC : ∀ᵐ w ∂P, ∀ s : NNReal, ContinuousWithinAt (fun u => Z u w) (Ici s) s)
    (rho : Omega → NNReal)
    (hStop : IsStoppingTime F (fun w => (rho w : WithTop NNReal)))
    (s : NNReal) (hBound : ∀ w, rho w ≤ s) :
    Measurable[F s] (fun w => Z (rho w) w) := by
  obtain ⟨G,hGs,hGc,hGl,hGu,hGt⟩ := boundedStoppingUpperGridV1 F rho hStop s hBound
  apply completedNaturalMeasurableAELimitV1 P X F hNatural s (fun k w => Z (G k w) w)
  · intro k
    exact boundedCountableStoppedStateMeasurableV1 F Z hAdapt (G k) (hGs k) (hGc k) s (hGu k)
  · filter_upwards [hRC] with w hw
    exact (hw (rho w)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hGt w,Eventually.of_forall fun k => hGl k w⟩)
