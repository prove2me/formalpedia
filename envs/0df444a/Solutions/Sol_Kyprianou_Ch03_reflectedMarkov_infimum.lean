-- Prove2me | solution 1 for Kyprianou.Ch03.reflectedMarkov_infimum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:47:31.739626+00:00
-- url     : https://prove2.me/submissions/c5b5c1ef-53ff-44d9-9dc4-6bed96f7546d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_reflectedSignedRestartAEV1
import Theorems.Thm_Kyprianou_Ch03_reflectedSignedStoppedKernelV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_ReflectedProcesses
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
  intro A hA f hf hBound t
  have hr := reflectedSignedRestartAEV1 P X hX (-1 : ℝ) y hy finiteTime t
  have hk := reflectedSignedStoppedKernelV1 P X hX (-1 : ℝ) y hy F hNatural
    tau hTau finiteTime hFinite A hA f hf hBound t
  have he : (∫ w in A ∩ {w | tau w ≠ ⊤},
      f (reflectedSup (fun s v => (-1 : ℝ) * X s v) y (finiteTime w + t) w) ∂P) =
    (∫ w in A ∩ {w | tau w ≠ ⊤},
      f (max (reflectedSup (fun s v => (-1 : ℝ) * X s v) y (finiteTime w) w)
        (LevyExtrema.SBA.runSup (fun s => (-1 : ℝ) * (X (finiteTime w+s) w - X (finiteTime w) w)) t)
          - (-1 : ℝ) * (X (finiteTime w+t) w - X (finiteTime w) w)) ∂P) := by
    apply integral_congr_ae
    filter_upwards [ae_mono Measure.restrict_le_self hr] with w hw
    exact congrArg f hw
  simpa only [neg_one_mul, sub_neg_eq_add, reflectedSup, reflectedInf] using he.trans hk
