-- Prove2me | solution 2 for Kyprianou.Ch03.reflectedMarkov_infimum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:49:03.512241+00:00
-- url     : https://prove2.me/submissions/7af7baf9-217a-4395-9981-3f91a9c29588
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
import Theorems.Thm_Kyprianou_Ch03_reflectedSignedRestartAEV1
import Theorems.Thm_Kyprianou_Ch03_reflectedSignedStoppedKernelV1
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
            f (reflectedInf X y (finiteTime omega + t) omega) ∂P) =
          (∫ omega in A ∩ {omega | tau omega ≠ ⊤},
            (∫ eta,
              f (max (reflectedInf X y (finiteTime omega) omega)
                    (LevyExtrema.SBA.runSup (fun s => -(X s eta)) t) +
                    X t eta) ∂P) ∂P) := by
  intro A hA f hf hb t
  have hr := reflectedSignedRestartAEV1 P X hX (-1) y hy finiteTime t
  have hk := reflectedSignedStoppedKernelV1 P X hX (-1) y hy F hNatural
    tau hTau finiteTime hFinite A hA f hf hb t
  have he := integral_congr_ae (μ := P.restrict (A ∩ {w | tau w ≠ ⊤}))
    ((ae_restrict_of_ae hr).mono fun w hw => congrArg f hw)
  simpa [neg_one_mul, reflectedInf, reflectedSup, sub_neg_eq_add] using he.trans hk


