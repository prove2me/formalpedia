-- Prove2me | solution 1 for Kyprianou.Ch04.finitePredictableTailBoxSecondMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:46:32.137245+00:00
-- url     : https://prove2.me/submissions/e3590fad-11fc-478d-9d74-77e8d2173e93

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableTailRectangleCovariance
import Theorems.Thm_Kyprianou_Ch04_finiteFamilyCovarianceExpansion
import Theorems.Thm_Kyprianou_Ch04_predictableWeightedPoissonBoxL2
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Second moment of a finite sum of predictable tail boxes, including overlaps. -/
theorem solution
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (s : Finset ι) (t : NNReal) (a : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hat : ∀ i ∈ s, a i ≤ t)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    let Z := fun i ω => H i ω *
      N.compensated (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i) ω
    Integrable (fun ω => (∑ i ∈ s, Z i ω)^2) P ∧
      (∫ ω, (∑ i ∈ s, Z i ω)^2 ∂P) =
      ∑ i ∈ s, ∑ j ∈ s, (∫ ω, H i ω * H j ω ∂P) *
        (referenceIntensity ν
          (Set.Ioc (↑(max (a i) (a j)) : ℝ) (t : ℝ) ×ˢ (B i ∩ B j))).toReal := by
  dsimp only
  let Z := fun i ω => H i ω *
    N.compensated (Set.Ioc (a i : ℝ) (t : ℝ) ×ˢ B i) ω
  have hcell (i : ι) (hi : i ∈ s) :=
    (Kyprianou.Ch04.predictableWeightedPoissonBoxL2
      P ν F N hFuture (a i) t (hat i hi) (B i) (hB i hi) (hFin i hi)
      (H i) (hH i hi) (hH2 i hi)).1
  have hZm (i : ι) (hi : i ∈ s) : AEStronglyMeasurable (Z i) P :=
    ((hH i hi).mono (F.le' (a i))).aestronglyMeasurable.mul
      ((ENNReal.measurable_toReal.comp
        (N.measurable_eval (measurableSet_Ioc.prod (hB i hi)))).sub_const _
      ).aestronglyMeasurable
  have hp (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :=
    Kyprianou.Ch04.integrableProductOfSquareIntegrable P (Z i) (Z j)
      (hZm i hi) (hZm j hj) (hcell i hi) (hcell j hj)
  change Integrable (fun ω => (∑ i ∈ s, Z i ω)^2) P ∧ _
  refine ⟨?_, ?_⟩
  · have hh : Integrable (fun ω => ∑ i ∈ s, ∑ j ∈ s, Z i ω * Z j ω) P :=
      integrable_finsetSum s (fun i hi => integrable_finsetSum s (fun j hj => hp i hi j hj))
    convert hh using 1
    ext ω
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  · rw [Kyprianou.Ch04.finiteFamilyCovarianceExpansion P s Z hp]
    refine Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => ?_))
    exact Kyprianou.Ch04.predictableTailRectangleCovariance
      P ν F N hFuture hPast (a i) (a j) t (hat i hi) (hat j hj)
      (B i) (B j) (hB i hi) (hB j hj) (hFin i hi) (hFin j hj)
      (H i) (H j) (hH i hi) (hH j hj) (hH2 i hi) (hH2 j hj)
