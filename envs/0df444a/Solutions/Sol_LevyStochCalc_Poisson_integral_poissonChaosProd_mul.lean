-- Prove2me | solution 1 for LevyStochCalc.Poisson.integral_poissonChaosProd_mul
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:39:36.347076+00:00
-- url     : https://prove2.me/submissions/aad483fc-61af-451d-82d9-bf08ca4e40e9

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaos_F001
import Definitions.Def_SourceProof_54f512cf38cabda215ff60d2

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open LevyStochCalc.Poisson

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (α β : Fin p → ℕ) :
    ∫ ω, poissonChaosProd N α B ω * poissonChaosProd N β B ω ∂P
      = if α = β then ∏ k, ((α k).factorial : ℝ) * (referenceIntensity ν (B k)).toReal ^ α k
        else 0 :=
  Prove2MeSourceProof.h_54f512cf38cabda215ff60d2 N hB hd hfin α β
