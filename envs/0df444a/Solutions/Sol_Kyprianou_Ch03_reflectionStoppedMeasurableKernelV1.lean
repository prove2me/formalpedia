-- Prove2me | solution 1 for Kyprianou.Ch03.reflectionStoppedMeasurableKernelV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:50:14.04963+00:00
-- url     : https://prove2.me/submissions/2c898673-dc50-4aea-a93a-11bfb8fc7524
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_reflectionProductKernelIntegralV1
import Theorems.Thm_Kyprianou_Ch03_reflectionStoppedStateRestrictedMeasV1
import Theorems.Thm_Kyprianou_Ch03_reflectionStoppedStateJointLawV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedRestrictedPathV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedPathV1
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
    (A : Set Omega)
    (hA : ∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    (S : Omega → ℝ)
    (hS : ∀ B : Set ℝ, MeasurableSet B → ∀ s : NNReal,
      MeasurableSet[F s] ({w | S w ∈ B} ∩ {w | tau w ≤ (s : WithTop NNReal)}))
    (H : ℝ × (NNReal → ℝ) → ℝ) (hH : Measurable H)
    (hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |H z| ≤ C) :
    (∫ w in A ∩ {w | tau w ≠ ⊤},
      H (S w, fun u => X (finiteTime w + u) w - X (finiteTime w) w) ∂P) =
    (∫ w in A ∩ {w | tau w ≠ ⊤},
      (∫ eta, H (S w, fun u => X u eta) ∂P) ∂P) := by 
  let mu := P.restrict (A ∩ {w | tau w ≠ ⊤})
  let Y : Omega → (NNReal → ℝ) := fun w u => X (finiteTime w+u) w - X (finiteTime w) w
  let Z : Omega → (NNReal → ℝ) := fun w u => X u w
  have hAdapt (u : NNReal) : Measurable[F u] (X u) := by
    apply (comap_measurable (X u)).mono _ le_rfl
    rw [hNatural u]
    exact le_sup_of_le_left (le_iSup₂_of_le u le_rfl le_rfl)
  have hZm : Measurable Z := measurable_pi_iff.mpr (fun u => (hAdapt u).mono (F.le u) le_rfl)
  obtain ⟨hY,_⟩ := strongMarkovExtendedRestrictedPathV1 P F X hX hNatural
    (strongMarkovDeterministicRestrictedPathV1 P F X hX hNatural) tau hTau finiteTime hFinite
  have hYm : AEMeasurable Y mu := hY.mono_measure
    (Measure.restrict_mono Set.inter_subset_right le_rfl)
  exact reflectionProductKernelIntegralV1 mu P S Y Z
    (reflectionStoppedStateRestrictedMeasV1 P F tau hTau A hA S hS) hYm hZm
    (reflectionStoppedStateJointLawV1 P X hX F hNatural tau hTau finiteTime hFinite A hA S hS)
    H hH hBound
