-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionStoppedStateRestrictedMeasV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:12:56.667116+00:00
-- url     : https://prove2.me/submissions/43874740-b3bf-4933-90e3-600f115762b7

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteStoppedEventMeasV1
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (A : Set Omega)
    (hA : ∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    (S : Omega → ℝ)
    (hS : ∀ B : Set ℝ, MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s] ({w | S w ∈ B} ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    : AEMeasurable S (P.restrict (A ∩ {w | tau w ≠ ⊤})) := by
  let E := A ∩ {w | tau w ≠ ⊤}
  have hE : MeasurableSet E := strongMarkovFiniteStoppedEventMeasV1 F tau hTau A hA
  have hFin (B : Set ℝ) (hB : MeasurableSet B) : MeasurableSet (E ∩ S ⁻¹' B) := by
    have hcut (s : NNReal) : MeasurableSet[F s]
        ((A ∩ S ⁻¹' B) ∩ {w | tau w ≤ (s : WithTop NNReal)}) := by
      simpa only [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm, Set.inter_self, Set.preimage] using
        (hA s).inter (hS B hB s)
    simpa only [E, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      strongMarkovFiniteStoppedEventMeasV1 F tau hTau (A ∩ S ⁻¹' B) hcut
  have hV : Measurable (E.indicator S) := by
    intro B hB
    by_cases hz : (0 : ℝ) ∈ B
    · rw [show (E.indicator S) ⁻¹' B = (E ∩ S ⁻¹' B) ∪ Eᶜ by
        ext w; by_cases hw : w ∈ E <;> simp [hw,hz]]
      exact (hFin B hB).union hE.compl
    · rw [show (E.indicator S) ⁻¹' B = E ∩ S ⁻¹' B by
        ext w; by_cases hw : w ∈ E <;> simp [hw,hz]]
      exact hFin B hB
  exact hV.aemeasurable.congr ((ae_restrict_mem hE).mono fun w hw => Set.indicator_of_mem hw S)
