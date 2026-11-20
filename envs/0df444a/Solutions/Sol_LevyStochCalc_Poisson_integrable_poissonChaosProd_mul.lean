-- Prove2me | solution 1 for LevyStochCalc.Poisson.integrable_poissonChaosProd_mul
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:39:34.357977+00:00
-- url     : https://prove2.me/submissions/ce0a7fbc-d424-4dfd-bc26-868282ddafa6

import Definitions.Def_LevyStochCalc_Poisson_SimpleChaos_F000
import Definitions.Def_SourceProof_2a94f92250093c132077f173

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open LevyStochCalc.Poisson

theorem solution {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (α β : Fin p → ℕ) :
    Integrable (fun ω => poissonChaosProd N α B ω * poissonChaosProd N β B ω) P :=
  Prove2MeSourceProof.h_2a94f92250093c132077f173 N hB hd hfin α β
