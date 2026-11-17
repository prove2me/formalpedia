-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prefix_bounded_event_probability
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:06:50.807759+00:00
-- url     : https://prove2.me/submissions/1f5ba94e-319e-4ff9-86fa-11e4a70c9d83

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

theorem poisson_prefix_bounded_event_probability
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (rate : ℕ → ℝ≥0) (N : ℕ → Ω → ℕ)
    (hN : ∀ k, AEMeasurable (N k) P)
    (hpref : ∀ n,
      P.map (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω) =
        poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k))
    (n m : ℕ) :
    P {ω | (∑ k ∈ Finset.range (n + 1), N k ω) ≤ m} =
      (poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k))
        (Set.Iic m) := by
  have hae : AEMeasurable (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω) P :=
    Finset.aemeasurable_fun_sum _ fun k _ => hN k
  rw [← hpref n, Measure.map_apply₀ hae (measurableSet_Iic.nullMeasurableSet)]
  rfl

end Kyprianou.ProofPreparation

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (rate : ℕ → ℝ≥0) (N : ℕ → Ω → ℕ)
    (hN : ∀ k, AEMeasurable (N k) P)
    (hpref : ∀ n,
      P.map (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω) =
        poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k))
    (n m : ℕ) :
    P {ω | (∑ k ∈ Finset.range (n + 1), N k ω) ≤ m} =
      (poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k))
        (Set.Iic m) := by
  first
  | exact Kyprianou.ProofPreparation.poisson_prefix_bounded_event_probability
  | exact Kyprianou.ProofPreparation.poisson_prefix_bounded_event_probability ..
  | (apply Kyprianou.ProofPreparation.poisson_prefix_bounded_event_probability <;> assumption)
