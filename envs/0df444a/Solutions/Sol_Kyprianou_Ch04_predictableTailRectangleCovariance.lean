-- Prove2me | solution 1 for Kyprianou.Ch04.predictableTailRectangleCovariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:40:48.441507+00:00
-- url     : https://prove2.me/submissions/393b654c-79e1-4706-8479-a04a5d0e9fa4

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_orderedPredictableTailRectangleCovariance
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Covariance of two arbitrary predictable tail rectangles. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (a b t : NNReal) (hat : a ≤ t) (hbt : b ≤ t)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAf : referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤)
    (hBf : referenceIntensity ν (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ B) ≠ ⊤)
    (H K : Ω → ℝ) (hH : StronglyMeasurable[F a] H) (hK : StronglyMeasurable[F b] K)
    (hH2 : Integrable (fun ω => (H ω)^2) P)
    (hK2 : Integrable (fun ω => (K ω)^2) P) :
    (∫ ω, (H ω * N.compensated (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ω) *
      (K ω * N.compensated (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ B) ω) ∂P) =
      (∫ ω, H ω * K ω ∂P) *
      (referenceIntensity ν (Set.Ioc (↑(max a b) : ℝ) (t : ℝ) ×ˢ (A ∩ B))).toReal := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    exact Kyprianou.Ch04.orderedPredictableTailRectangleCovariance
      P ν F N hFuture hPast a b t hab hbt A B hA hB hAf hBf H K hH hK hH2 hK2
  · rw [max_eq_left hba]
    have h := Kyprianou.Ch04.orderedPredictableTailRectangleCovariance
      P ν F N hFuture hPast b a t hba hat B A hB hA hBf hAf K H hK hH hK2 hH2
    simpa only [Set.inter_comm B A, mul_comm (K _) (H _),
      mul_comm (K _ * N.compensated _ _) (H _ * N.compensated _ _)] using h
