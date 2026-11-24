-- Prove2me | solution 1 for Kyprianou.Ch03.reflectedSignedStoppedKernelV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:02:29.950799+00:00
-- url     : https://prove2.me/submissions/e9f695b2-7bef-4776-8f41-782bea27fa8b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_reflectionStoppedStateCutsMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_reflectionFutureSupProxyAEV1
import Theorems.Thm_Kyprianou_Ch03_reflectionStoppedMeasurableKernelV1
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
    (X : NNReal → Omega → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (c y : ℝ) (hy : 0 ≤ y)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : IsCompletedNaturalFiltration P X F)
    (tau : Omega → WithTop NNReal) (hTau : IsStoppingTime F tau)
    (finiteTime : Omega → NNReal)
    (hFinite : ∀ w, tau w ≠ ⊤ → tau w = (finiteTime w : WithTop NNReal))
    (A : Set Omega)
    (hA : ∀ s : NNReal, MeasurableSet[F s]
      (A ∩ {w : Omega | tau w ≤ (s : WithTop NNReal)}))
    (f : ℝ → ℝ) (hf : Measurable f)
    (hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |f z| ≤ C)
    (t : NNReal)
    :
    (∫ w in A ∩ {w | tau w ≠ ⊤},
      f (max (reflectedSup (fun s v => c * X s v) y (finiteTime w) w)
          (LevyExtrema.SBA.runSup (fun s => c * (X (finiteTime w + s) w - X (finiteTime w) w)) t)
          - c * (X (finiteTime w + t) w - X (finiteTime w) w)) ∂P) =
    (∫ w in A ∩ {w | tau w ≠ ⊤},
      (∫ eta, f (max (reflectedSup (fun s v => c * X s v) y (finiteTime w) w)
          (LevyExtrema.SBA.runSup (fun s => c * X s eta) t) - c * X t eta) ∂P) ∂P) := by 
  obtain ⟨K,hK,hFresh,hShift⟩ := reflectionFutureSupProxyAEV1 P X hX finiteTime c t
  let S := fun w => reflectedSup (fun s v => c * X s v) y (finiteTime w) w
  let H : ℝ × (NNReal → ℝ) → ℝ := fun z => f (max z.1 (K z.2) - c * z.2 t)
  have hH : Measurable H := hf.comp
    ((measurable_fst.max (hK.comp measurable_snd)).sub
      (measurable_const.mul ((measurable_pi_apply t).comp measurable_snd)))
  obtain ⟨C,hC,hfC⟩ := hBound
  have hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |H z| ≤ C := ⟨C,hC,fun z => hfC _⟩
  have hk := reflectionStoppedMeasurableKernelV1 P X hX F hNatural tau hTau finiteTime
    hFinite A hA S (reflectionStoppedStateCutsMeasurableV1 P X hX F hNatural tau hTau
      finiteTime hFinite c y) H hH hB
  have hL : (∫ w in A ∩ {w | tau w ≠ ⊤},
      f (max (S w) (LevyExtrema.SBA.runSup
        (fun s => c * (X (finiteTime w + s) w - X (finiteTime w) w)) t)
        - c * (X (finiteTime w + t) w - X (finiteTime w) w)) ∂P) =
      (∫ w in A ∩ {w | tau w ≠ ⊤},
        H (S w, fun u => X (finiteTime w + u) w - X (finiteTime w) w) ∂P) := by
    apply integral_congr_ae
    filter_upwards [ae_mono Measure.restrict_le_self hShift] with w hw
    simp only [H, hw]
  have hR : (∫ w in A ∩ {w | tau w ≠ ⊤},
      (∫ eta, H (S w, fun u => X u eta) ∂P) ∂P) =
      (∫ w in A ∩ {w | tau w ≠ ⊤},
        (∫ eta, f (max (S w) (LevyExtrema.SBA.runSup (fun s => c * X s eta) t)
          - c * X t eta) ∂P) ∂P) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w
    apply integral_congr_ae
    filter_upwards [hFresh] with eta he
    simp only [H, he]
  exact hL.trans (hk.trans hR)
