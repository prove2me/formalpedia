-- Prove2me | solution 1 for Kyprianou.Ch03.completedNaturalStoppedAdaptedEventsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:20:08.15685+00:00
-- url     : https://prove2.me/submissions/95967b7a-c3aa-4c39-bb8e-afad53dda208

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_Kyprianou_Ch03_completedNaturalMeasurableAEModV1
import Theorems.Thm_Kyprianou_Ch03_boundedStoppingUpperGridV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCountableFibreMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteStoppedEventMeasV1
import Theorems.Thm_Kyprianou_Ch03_completedNaturalClippedStateMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_finiteStoppingClipV1
import Theorems.Thm_Kyprianou_Ch03_reflectionStoppedStateRestrictedMeasV1
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
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (r : Omega → NNReal) (hr : ∀ w, tau w ≠ ⊤ → tau w = (r w : WithTop NNReal))
    (A : Set Omega)
    (hA : ∀ s : NNReal, MeasurableSet[F s] (A ∩ {w | tau w ≤ (s : WithTop NNReal)})) :
    AEMeasurable (fun w => Z (r w) w) (P.restrict (A ∩ {w | tau w ≠ ⊤})) ∧
    ∀ (B : Set ℝ), MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s] ((A ∩ {w | Z (r w) w ∈ B}) ∩
        {w | tau w ≤ (s : WithTop NNReal)}) := by
  let S (w : Omega) := Z (r w) w
  have hcut (B : Set ℝ) (hB : MeasurableSet B) (s : NNReal) :
      MeasurableSet[F s] ({w | S w ∈ B} ∩ {w | tau w ≤ (s : WithTop NNReal)}) := by
    obtain ⟨rho,hStop,hR,hEq⟩ := finiteStoppingClipV1 F tau hTau r hr s
    have hW := completedNaturalClippedStateMeasurableV1 P X F hNatural Z hAdapt hRC rho
      hStop s hR
    apply completedNaturalMeasurableAEModV1 P F X hNatural s _
      ((fun w => Z (rho w) w) ⁻¹' B ∩ {w | tau w ≤ (s : WithTop NNReal)})
      ((hW hB).inter (hTau s))
    filter_upwards with w
    by_cases hw : tau w ≤ (s : WithTop NNReal)
    · simp [S,hw,hEq w hw]
    · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
      exact iff_of_false (fun h => hw h.2) (fun h => hw h.2)
  refine ⟨reflectionStoppedStateRestrictedMeasV1 P F tau hTau A hA S hcut, ?_⟩
  intro B hB s
  have he : (A ∩ {w | tau w ≤ (s : WithTop NNReal)}) ∩
      ({w | S w ∈ B} ∩ {w | tau w ≤ (s : WithTop NNReal)}) =
      (A ∩ {w | Z (r w) w ∈ B}) ∩ {w | tau w ≤ (s : WithTop NNReal)} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, S]
    tauto
  rw [← he]
  exact (hA s).inter (hcut B hB s)
