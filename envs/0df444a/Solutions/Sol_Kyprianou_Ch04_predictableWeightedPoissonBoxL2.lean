-- Prove2me | solution 1 for Kyprianou.Ch04.predictableWeightedPoissonBoxL2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:00:29.018822+00:00
-- url     : https://prove2.me/submissions/2a48700c-512f-40bc-a5fc-8d679aa7e2a1

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_pastWeightedPoissonBoxSquareMoment
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped ENNReal NNReal
set_option autoImplicit false

/-- A predictable weighted compensated box has the intensity-scaled second moment. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (u t : NNReal) (hut : u ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hFin : referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (H : Ω → ℝ) (hH : StronglyMeasurable[F u] H)
    (hH2 : Integrable (fun ω => (H ω)^2) P) :
    Integrable (fun ω => (H ω * N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω)^2) P ∧
    (∫ ω, (H ω * N.compensated (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B) ω)^2 ∂P) =
      (referenceIntensity ν (Set.Ioc (u : ℝ) (t : ℝ) ×ˢ B)).toReal *
        ∫ ω, (H ω)^2 ∂P := by
  obtain ⟨hi, he⟩ := Kyprianou.Ch04.pastWeightedPoissonBoxSquareMoment
    P ν F N hFuture u t hut B hB hFin (fun ω => (H ω)^2)
    (hH.measurable.pow_const (2 : ℕ)).stronglyMeasurable hH2
  refine ⟨?_, ?_⟩
  · simpa only [mul_pow] using hi
  · simpa only [mul_pow, mul_comm] using he
