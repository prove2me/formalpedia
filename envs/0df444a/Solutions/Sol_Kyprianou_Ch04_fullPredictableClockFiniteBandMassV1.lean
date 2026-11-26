-- Prove2me | solution 1 for Kyprianou.Ch04.fullPredictableClockFiniteBandMassV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:08:07.670548+00:00
-- url     : https://prove2.me/submissions/cb2b0f30-41ea-4d70-b9b6-b91f2f0dd6a6

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The full predictable clock gives finite mass to every finite intensity mark band. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (t : NNReal)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    [mAll : MeasurableSpace ((NNReal × Ω) × ℝ)]
    (hAll : mAll = F.predictable.prod inferInstance)
    (μ : Measure ((NNReal × Ω) × ℝ))
    (hClock : ∀ f : ((NNReal × Ω) × ℝ) → ENNReal, Measurable f →
      (∫⁻ p, f p ∂μ) = ∫⁻ w, ∫⁻ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν ∂P) :
    μ (univ ×ˢ B) < ⊤ := by
  let S : Set ((NNReal × Ω) × ℝ) := univ ×ˢ B
  have hs : MeasurableSet S := by
    rw [hAll]
    exact MeasurableSet.univ.prod hB
  let f := S.indicator (fun _ => (1 : ENNReal))
  have hf : Measurable f := measurable_const.indicator hs
  have hL : (∫⁻ p, f p ∂μ) = μ S := by
    simp [f,lintegral_indicator hs]
  have hR (w : Ω) : (∫⁻ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
      f ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν) =
      referenceIntensity ν (Icc (0 : ℝ) (t : ℝ) ×ˢ B) := by
    have he : (fun z : ℝ × ℝ => f ((z.1.toNNReal,w),z.2)) =
        (univ ×ˢ B).indicator (fun _ => (1 : ENNReal)) := by
      funext z
      by_cases hz : z.2 ∈ B
      · have h1 : ((z.1.toNNReal,w),z.2) ∈ S := ⟨mem_univ _,hz⟩
        have h2 : z ∈ univ ×ˢ B := ⟨mem_univ _,hz⟩
        simp [f,Set.indicator_of_mem h1,Set.indicator_of_mem h2]
      · have h1 : ((z.1.toNNReal,w),z.2) ∉ S := fun h => hz h.2
        have h2 : z ∉ univ ×ˢ B := fun h => hz h.2
        simp [f,Set.indicator_of_notMem h1,Set.indicator_of_notMem h2]
    rw [he,lintegral_indicator (MeasurableSet.univ.prod hB),lintegral_const,
      Measure.restrict_apply MeasurableSet.univ]
    simp [Measure.restrict_apply (MeasurableSet.univ.prod hB), inter_comm,
      Set.prod_inter_prod]
  rw [← hL, hClock f hf]
  simp_rw [hR]
  simpa using Kyprianou.Ch04.closedTimeBandIntensityFinite ν t B hfin |>.lt_top
