-- Prove2me | solution 1 for Kyprianou.Ch04.finitePredictableMarkedGridIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:25:43.144533+00:00
-- url     : https://prove2.me/submissions/4356777a-ac52-49f1-8acb-da7ca7ec5224

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableWeightedPoissonBoxL2
import Theorems.Thm_Kyprianou_Ch04_weightedDisjointGridBoxCrossZero
import Theorems.Thm_Kyprianou_Ch04_orthogonalFiniteFamilyL2Identity
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Isometry for arbitrary finite disjoint predictable time-mark grid cells. -/
theorem solution
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (u : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ → Measurable[F u] (fun ω => N.N ω B))
    (s : Finset ι) (a b : ι → NNReal) (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (Set.Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P)
    (hGrid : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      b i ≤ a j ∨ b j ≤ a i ∨ (a i = a j ∧ b i = b j ∧ Disjoint (B i) (B j))) :
    ∫ ω, (∑ i ∈ s, H i ω *
      N.compensated (Set.Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i) ω)^2 ∂P =
      ∑ i ∈ s, (referenceIntensity ν (Set.Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i)).toReal *
        ∫ ω, (H i ω)^2 ∂P := by
  let Z := fun i ω => H i ω * N.compensated (Set.Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i) ω
  have hcell (i : ι) (hi : i ∈ s) := Kyprianou.Ch04.predictableWeightedPoissonBoxL2
    P ν F N hFuture (a i) (b i) (hab i hi) (B i) (hB i hi) (hFin i hi)
    (H i) (hH i hi) (hH2 i hi)
  have hZm (i : ι) (hi : i ∈ s) : AEStronglyMeasurable (Z i) P :=
    ((hH i hi).mono (F.le' (a i))).aestronglyMeasurable.mul
      ((ENNReal.measurable_toReal.comp
        (N.measurable_eval (measurableSet_Ioc.prod (hB i hi)))).sub_const _).aestronglyMeasurable
  have hprod (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :=
    Kyprianou.Ch04.integrableProductOfSquareIntegrable P (Z i) (Z j)
      (hZm i hi) (hZm j hj) (hcell i hi).1 (hcell j hj).1
  have horth (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) (hn : i ≠ j) :=
    Kyprianou.Ch04.weightedDisjointGridBoxCrossZero P ν F N hFuture hPast
      (a i) (b i) (a j) (b j) (hab i hi) (hab j hj) (B i) (B j) (hB i hi) (hB j hj)
      (hFin i hi) (hFin j hj) (hGrid i hi j hj hn) (H i) (H j)
      (hH i hi) (hH j hj) (hH2 i hi) (hH2 j hj) (hcell i hi).1 (hcell j hj).1
  change (∫ ω, (∑ i ∈ s, Z i ω)^2 ∂P) = _
  rw [Kyprianou.Ch04.orthogonalFiniteFamilyL2Identity P s Z hprod horth]
  exact Finset.sum_congr rfl (fun i hi => (hcell i hi).2)
