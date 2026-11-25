-- Prove2me | solution 1 for Kyprianou.Ch04.finiteWeightedPoissonCellIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:00:16.654467+00:00
-- url     : https://prove2.me/submissions/767f57fd-bf4f-4add-8ba1-c3034ee10200

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_orthogonalFiniteFamilyL2Identity
import Theorems.Thm_Kyprianou_Ch04_independentWeightedPoissonCellIsometry
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite weighted Poisson-box isometry from diagonal moments and orthogonality. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    {ι : Type} [DecidableEq ι]
    (s : Finset ι) (B : ι → Set (ℝ × ℝ)) (H : ι → Ω → ℝ)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFin : ∀ i ∈ s, referenceIntensity ν (B i) ≠ ⊤)
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω) ^ 2) P)
    (hIndep : ∀ i ∈ s, IndepFun (H i) (fun ω => N.N ω (B i)) P)
    (hProd : ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun ω => (H i ω * N.compensated (B i) ω) *
        (H j ω * N.compensated (B j) ω)) P)
    (hOrth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∫ ω, (H i ω * N.compensated (B i) ω) *
        (H j ω * N.compensated (B j) ω) ∂P = 0) :
    ∫ ω, (∑ i ∈ s, H i ω * N.compensated (B i) ω) ^ 2 ∂P =
      ∑ i ∈ s, (referenceIntensity ν (B i)).toReal *
        ∫ ω, (H i ω) ^ 2 ∂P := by
  calc
    ∫ ω, (∑ i ∈ s, H i ω * N.compensated (B i) ω) ^ 2 ∂P =
        ∑ i ∈ s, ∫ ω, (H i ω * N.compensated (B i) ω) ^ 2 ∂P := by
      exact Kyprianou.Ch04.orthogonalFiniteFamilyL2Identity P s
        (fun i ω => H i ω * N.compensated (B i) ω) hProd hOrth
    _ = ∑ i ∈ s, (referenceIntensity ν (B i)).toReal *
        ∫ ω, (H i ω) ^ 2 ∂P := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (Kyprianou.Ch04.independentWeightedPoissonCellIsometry
        P ν N (hB i hi) (hFin i hi) (H i) (hH2 i hi) (hIndep i hi)).2
