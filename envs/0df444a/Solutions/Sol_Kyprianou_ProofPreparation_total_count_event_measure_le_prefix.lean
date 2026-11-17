-- Prove2me | solution 1 for Kyprianou.ProofPreparation.total_count_event_measure_le_prefix
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:02:08.630262+00:00
-- url     : https://prove2.me/submissions/0cc13746-c612-4f62-a7a9-8a03521ce460

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
set_option autoImplicit false


namespace Kyprianou.ProofPreparation

theorem total_count_event_measure_le_prefix
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ → Ω → ℕ)
    (n m : ℕ) :
    P {ω | (∑' k, ((N k ω : ℕ) : ENNReal)) ≤ m} ≤
      P {ω | (∑ k ∈ Finset.range (n + 1), N k ω) ≤ m} := by
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have h1 : ((∑ k ∈ Finset.range (n + 1), N k ω : ℕ) : ENNReal) ≤ m := by
    push_cast
    exact (ENNReal.sum_le_tsum _).trans hω
  exact_mod_cast h1

end Kyprianou.ProofPreparation

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ → Ω → ℕ)
    (n m : ℕ) :
    P {ω | (∑' k, ((N k ω : ℕ) : ENNReal)) ≤ m} ≤
      P {ω | (∑ k ∈ Finset.range (n + 1), N k ω) ≤ m} := by
  first
  | exact Kyprianou.ProofPreparation.total_count_event_measure_le_prefix
  | exact Kyprianou.ProofPreparation.total_count_event_measure_le_prefix ..
  | (apply Kyprianou.ProofPreparation.total_count_event_measure_le_prefix <;> assumption)
