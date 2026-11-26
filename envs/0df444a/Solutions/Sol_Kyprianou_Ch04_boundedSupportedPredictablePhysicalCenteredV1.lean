-- Prove2me | solution 1 for Kyprianou.Ch04.boundedSupportedPredictablePhysicalCenteredV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:18:53.179774+00:00
-- url     : https://prove2.me/submissions/c6a175d6-a810-4566-9e56-8402874a7743

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_fullPredictableClockAgreement
import Theorems.Thm_Kyprianou_Ch04_fullPredictableClockFiniteBandMassV1
import Theorems.Thm_Kyprianou_Ch04_boundedFiniteSupportMemLpV1
import Theorems.Thm_Kyprianou_Ch04_markedPredictableLeAmbientProduct
import Theorems.Thm_Kyprianou_Ch04_sharedClockSignedIntegralV1
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Bounded marked predictable kernels of finite mark support are centred after compensation. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal inferInstance) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (T : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC : ∀ p, ‖g p‖ ≤ C) (hs : ∀ p, p.2 ∉ B → g p = 0) :
    let U := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
    let J := fun ω => (∫ z in U, g ((z.1.toNNReal,ω),z.2) ∂(N.N ω)) -
      ∫ z in U, g ((z.1.toNNReal,ω),z.2) ∂referenceIntensity ν
    Integrable J P ∧ (∫ ω, J ω ∂P) = 0 := by
  let U := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
  obtain ⟨μ,hClock⟩ := Kyprianou.Ch04.fullPredictableClockAgreement P ν F N hFuture T
  letI : MeasurableSpace ((NNReal × Ω) × ℝ) := F.predictable.prod inferInstance
  have hmass := Kyprianou.Ch04.fullPredictableClockFiniteBandMassV1
    P ν F T B hB hfin rfl μ (fun f hf => (hClock f hf).2.2.2)
  have hp := Kyprianou.Ch04.boundedFiniteSupportMemLpV1 μ (univ ×ˢ B)
    (MeasurableSet.univ.prod hB) hmass g hg C hC
    (fun p hp => hs p (fun hb => hp ⟨mem_univ _,hb⟩))
  let q := fun (ω : Ω) (z : ℝ × ℝ) => ((z.1.toNNReal,ω),z.2)
  have hq (ω : Ω) : Measurable (q ω) := by
    have hm : @Measurable (ℝ × ℝ) ((NNReal × Ω) × ℝ) inferInstance
        (((inferInstance : MeasurableSpace NNReal).prod
          (inferInstance : MeasurableSpace Ω)).prod (inferInstance : MeasurableSpace ℝ))
        (q ω) :=
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
        measurable_const).prodMk measurable_snd
    exact hm.mono le_rfl (Kyprianou.Ch04.markedPredictableLeAmbientProduct F)
  have r := Kyprianou.Ch04.sharedClockSignedIntegralV1 P μ
    (fun ω => (N.N ω).restrict U) q hq
    (fun f hf => ⟨(hClock f hf).1,(hClock f hf).2.2.1.symm⟩) g hg hp.1
  have c := Kyprianou.Ch04.sharedClockSignedIntegralV1 P μ
    (fun _ => (referenceIntensity ν).restrict U) q hq
    (fun f hf => ⟨(hClock f hf).2.1,(hClock f hf).2.2.2.symm⟩) g hg hp.1
  refine ⟨r.2.1.sub c.2.1,?_⟩
  rw [integral_sub r.2.1 c.2.1,r.2.2,c.2.2,sub_self]
