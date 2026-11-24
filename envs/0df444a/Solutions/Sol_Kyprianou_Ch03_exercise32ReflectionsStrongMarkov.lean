-- Prove2me | solution 1 for Kyprianou.Ch03.exercise32ReflectionsStrongMarkov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:01:36.90307+00:00
-- url     : https://prove2.me/submissions/0d8b21a7-0d55-4dac-b0de-965a0a757d17

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_Kyprianou_Ch03_reflectedMarkov_supremum
import Theorems.Thm_Kyprianou_Ch03_reflectedMarkov_infimum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03


theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (y : ℝ) (hy : 0 ≤ y)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ omega, tau omega ≠ ⊤ →
      tau omega = (finiteTime omega : WithTop NNReal)) :
    ∀ A : Set Omega,
      (∀ s : NNReal, MeasurableSet[F s]
        (A ∩ {omega : Omega | tau omega ≤ (s : WithTop NNReal)})) →
      ∀ f : ℝ → ℝ, Measurable f →
        (∃ C : ℝ, 0 ≤ C ∧ ∀ z, |f z| ≤ C) →
        ∀ t : NNReal,
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            f (reflectedSup X y (finiteTime omega + t) omega) ∂P) =
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            (∫ eta,
              f (max (reflectedSup X y (finiteTime omega) omega)
                    (LevyExtrema.SBA.runSup (fun s => X s eta) t) -
                    X t eta) ∂P) ∂P) ∧
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            f (reflectedInf X y (finiteTime omega + t) omega) ∂P) =
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            (∫ eta,
              f (max (reflectedInf X y (finiteTime omega) omega)
                    (LevyExtrema.SBA.runSup (fun s => -(X s eta)) t) +
                    X t eta) ∂P) ∂P) := by
  intro A hA f hf hb t
  exact ⟨
    Kyprianou.Ch03.reflectedMarkov_supremum P F X hX hNatural y hy tau hTau finiteTime hFinite A hA f hf hb t,
    Kyprianou.Ch03.reflectedMarkov_infimum P F X hX hNatural y hy tau hTau finiteTime hFinite A hA f hf hb t
  ⟩

