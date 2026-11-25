-- Prove2me | solution 1 for Kyprianou.Ch04.finiteMarkedClockMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:00:53.192056+00:00
-- url     : https://prove2.me/submissions/a56a2292-b5de-4e50-b83a-a6a9e221d963

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_localFiniteMarkedKernel
import Theorems.Thm_Kyprianou_Ch04_finiteKernelMarkedPushforwardMeasurable
import Theorems.Thm_Kyprianou_Ch04_predictableMarkedProductLeAmbient
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (R : Omega → Measure (Real × Real))
    (hR : ∀ S : Set (Real × Real), MeasurableSet S →
      Measurable (fun w => R w S))
    (t : NNReal) (B : Set Real) (hB : MeasurableSet B)
    (hFin : ∀ᵐ w ∂P, R w (Set.Icc (0 : Real) (t : Real) ×ˢ B) ≠ ⊤) :
    ∃ M : @Measure ((NNReal × Omega) × Real) (F.predictable.prod inferInstance),
      ∀ f : ((NNReal × Omega) × Real) → ENNReal, Measurable[F.predictable.prod inferInstance] f →
        AEMeasurable (fun w => ∫⁻ z in (Set.Icc (0 : Real) (t : Real) ×ˢ B),
          f ((z.1.toNNReal, w), z.2) ∂(R w)) P ∧
        (∫⁻ p, f p ∂M) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ B,
        f ((z.1.toNNReal, w), z.2) ∂(R w) ∂P) := by
  let U : Set (Real × Real) := Set.Icc (0 : Real) (t : Real) ×ˢ B
  obtain ⟨κ, hκ, hκeq⟩ := localFiniteMarkedKernel P R hR U (measurableSet_Icc.prod hB) hFin
  let K : Omega → Measure ((NNReal × Omega) × Real) := fun w =>
    Measure.map (fun z => ((z.1.toNNReal, w), z.2)) (κ w)
  have hK : Measurable K := finiteKernelMarkedPushforwardMeasurable κ hκ
  have hle := predictableMarkedProductLeAmbient F
  refine ⟨(P.bind K).trim hle, fun f hf => ?_⟩
  have hf0 : Measurable f := hf.mono hle le_rfl
  have he : (fun w => ∫⁻ p, f p ∂(K w)) =ᵐ[P]
      (fun w => ∫⁻ z in U, f ((z.1.toNNReal, w), z.2) ∂(R w)) := by
    filter_upwards [hκeq] with w hw
    have hJ : Measurable (fun z : Real × Real => ((z.1.toNNReal, w), z.2)) :=
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
        measurable_const).prodMk measurable_snd
    change (∫⁻ p, f p ∂(Measure.map (fun z => ((z.1.toNNReal, w), z.2)) (κ w))) = _
    rw [lintegral_map hf0 hJ, hw]
  refine ⟨((Measure.measurable_lintegral hf0).comp hK).aemeasurable.congr he, ?_⟩
  rw [lintegral_trim hle hf, Measure.lintegral_bind hK.aemeasurable hf0.aemeasurable]
  exact lintegral_congr_ae he
