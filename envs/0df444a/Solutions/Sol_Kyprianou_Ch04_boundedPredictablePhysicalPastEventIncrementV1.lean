-- Prove2me | solution 1 for Kyprianou.Ch04.boundedPredictablePhysicalPastEventIncrementV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:43:17.65753+00:00
-- url     : https://prove2.me/submissions/56f8499a-e896-43da-986a-dde2485ba7bc

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedPredictablePhysicalCenteredV1
import Theorems.Thm_Kyprianou_Ch04_predictablePastEventTimeMaskV1
import Theorems.Thm_Kyprianou_Ch04_physicalPastEventIntervalIncrementV1
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Conditional centring follows from compensation of the past-event masked increment. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal inferInstance) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (g : (NNReal × Ω) × ℝ → ℝ)
    (hg : Measurable[F.predictable.prod inferInstance] g)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ p, ‖g p‖ ≤ C)
    (hsupp : ∀ p, p.2 ∉ B → g p = 0)
    (s t : NNReal) (hst : s ≤ t) (A : Set Ω) (hA : MeasurableSet[F s] A)
    (hi : ∀ᵐ w ∂P,
      IntegrableOn (fun z : ℝ × ℝ => g ((z.1.toNNReal,w),z.2))
        (Icc (0 : ℝ) (t : ℝ) ×ˢ univ) (N.N w) ∧
      IntegrableOn (fun z : ℝ × ℝ => g ((z.1.toNNReal,w),z.2))
        (Icc (0 : ℝ) (t : ℝ) ×ˢ univ) (referenceIntensity ν)) :
    let J := fun (u : NNReal) w =>
      (∫ z in Icc (0 : ℝ) (u : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in Icc (0 : ℝ) (u : ℝ) ×ˢ univ, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
    (∫ w in A, J s w ∂P) = ∫ w in A, J t w ∂P := by
  classical
  let U (u : NNReal) := Icc (0 : ℝ) (u : ℝ) ×ˢ (univ : Set ℝ)
  let J := fun (u : NNReal) w =>
    (∫ z in U u, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
    ∫ z in U u, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν
  let D := (Ioc s t ×ˢ A) ×ˢ (univ : Set ℝ)
  let k := D.indicator g
  have hk := Kyprianou.Ch04.predictablePastEventTimeMaskV1 F s t A hA g hg
  have hb : ∀ p, ‖k p‖ ≤ C := fun p => (norm_indicator_le_norm_self (s := D) g p).trans (hC p)
  have hs : ∀ p, p.2 ∉ B → k p = 0 := fun p hp => by
    simp [k, Set.indicator_apply, hsupp p hp]
  have hc := Kyprianou.Ch04.boundedSupportedPredictablePhysicalCenteredV1 P ν F N
    hFuture t B hB hfin k hk C hb hs
  have he : (fun w => (∫ z in U t, k ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in U t, k ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν) =ᵐ[P]
      A.indicator (fun w => J t w - J s w) := by
    filter_upwards [hi] with w hw
    change (∫ z in U t, k ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      (∫ z in U t, k ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν) = _
    rw [Kyprianou.Ch04.physicalPastEventIntervalIncrementV1 (N.N w) s t hst A g w hw.1,
      Kyprianou.Ch04.physicalPastEventIntervalIncrementV1 (referenceIntensity ν) s t hst A g w hw.2]
    by_cases hwA : w ∈ A <;> simp [hwA,J,U] <;> ring
  have hz : (∫ w in A, J t w - J s w ∂P) = 0 := by
    rw [← integral_indicator (F.le s A hA), ← integral_congr_ae he]
    exact hc.2
  have ht := (Kyprianou.Ch04.boundedSupportedPredictablePhysicalCenteredV1 P ν F N
    hFuture t B hB hfin g hg C hC hsupp).1
  have hs' := (Kyprianou.Ch04.boundedSupportedPredictablePhysicalCenteredV1 P ν F N
    hFuture s B hB hfin g hg C hC hsupp).1
  change (∫ w in A, J s w ∂P) = ∫ w in A, J t w ∂P
  rw [integral_sub ht.integrableOn hs'.integrableOn] at hz
  linarith
