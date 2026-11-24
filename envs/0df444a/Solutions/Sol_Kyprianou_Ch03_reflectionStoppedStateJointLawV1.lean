-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionStoppedStateJointLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:12:48.295224+00:00
-- url     : https://prove2.me/submissions/41e9f4b9-2dda-4262-9d86-945258ecb0a3

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_Kyprianou_Ch03_reflectionStoppedStateRestrictedMeasV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedRestrictedPathV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedPathV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteStoppedEventMeasV1
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
    (A : Set Omega)
    (hA : ∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    (S : Omega → ℝ)
    (hS : ∀ B : Set ℝ, MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s] ({w | S w ∈ B} ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    :
    Measure.map (fun w => (S w, (fun w u => X (finiteTime w + u) w - X (finiteTime w) w) w)) (P.restrict (A ∩ {w | tau w ≠ ⊤})) =
      (Measure.map S (P.restrict (A ∩ {w | tau w ≠ ⊤}))).prod (Measure.map (fun w u => X u w) P) := by
  let E := A ∩ {w | tau w ≠ ⊤}
  let Q := P.restrict E
  let U (w : Omega) (u : NNReal) := X (finiteTime w+u) w - X (finiteTime w) w
  let V (w : Omega) (u : NNReal) := X u w
  have hs := reflectionStoppedStateRestrictedMeasV1 P F tau hTau A hA S hS
  have hSM := strongMarkovExtendedRestrictedPathV1 P F X hX hNatural
    (strongMarkovDeterministicRestrictedPathV1 P F X hX hNatural) tau hTau finiteTime hFinite
  have hu : AEMeasurable U Q :=
    hSM.1.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
  apply Measure.ext_prod
  intro B C hB hC
  have hcut (s : NNReal) : MeasurableSet[F s]
      ((A ∩ S ⁻¹' B) ∩ {w | tau w ≤ (s : WithTop NNReal)}) := by
    simpa only [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm, Set.inter_self, Set.preimage] using
      (hA s).inter (hS B hB s)
  have hLaw : Measure.map U (P.restrict (E ∩ S ⁻¹' B)) =
      P (E ∩ S ⁻¹' B) • Measure.map V P := by
    simpa only [E,Set.inter_assoc,Set.inter_left_comm,Set.inter_comm] using
      hSM.2 (A ∩ S ⁻¹' B) hcut
  have hUR := hu.mono_measure
    (Measure.restrict_mono (Set.inter_subset_left : E ∩ S ⁻¹' B ⊆ E) le_rfl)
  have h := congrArg (fun μ : Measure (NNReal → ℝ) => μ C) hLaw
  rw [Measure.map_apply_of_aemeasurable hUR hC, Measure.smul_apply, smul_eq_mul] at h
  rw [Measure.map_apply_of_aemeasurable (hs.prodMk hu) (hB.prod hC), Measure.prod_prod]
  change Q (S ⁻¹' B ∩ U ⁻¹' C) = Q.map S B * P.map V C
  rw [Measure.map_apply_of_aemeasurable hs hB]
  have hE := strongMarkovFiniteStoppedEventMeasV1 F tau hTau A hA
  rw [show Q (S ⁻¹' B) = P (E ∩ S ⁻¹' B) by
    exact (Measure.restrict_apply' hE).trans (by rw [Set.inter_comm])]
  rw [← h, Set.inter_comm E (S ⁻¹' B), ← Measure.restrict_restrict' hE]
  change Q (S ⁻¹' B ∩ U ⁻¹' C) = (Q.restrict (S ⁻¹' B)) (U ⁻¹' C)
  have hn : NullMeasurableSet (U ⁻¹' C) (Q.restrict (S ⁻¹' B)) := by
    rw [Measure.restrict_restrict' hE, Set.inter_comm]
    exact hUR.nullMeasurableSet_preimage hC
  rw [Measure.restrict_apply₀ hn, Set.inter_comm]
