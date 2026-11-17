-- Prove2me | solution 1 for Kyprianou.ProofPreparation.exercise2_1_infinite_rate_divergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:48:58.992742+00:00
-- url     : https://prove2.me/submissions/18552f9e-dc68-4ab1-a623-36c36393e0a6

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_aemeasurable_of_poisson_law
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prefix_sum_law
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prefix_rate_diverges
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_bounded_count_probability_tendsto_zero
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prefix_bounded_event_probability
import Theorems.Thm_Kyprianou_ProofPreparation_total_count_event_measure_le_prefix
import Theorems.Thm_Kyprianou_ProofPreparation_measure_null_of_upper_bounds_tendsto_zero
import Theorems.Thm_Kyprianou_ProofPreparation_ae_top_of_null_all_finite_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P)
    (hdiv : (∑' k, (rate k : ENNReal)) = ⊤) :
    ∀ᵐ w ∂P, (∑' k, ((N k w : Nat) : ENNReal)) = ⊤ := by
  have hm : forall k, AEMeasurable (N k) P :=
    fun k => aemeasurable_of_poisson_law P (rate k) (N k) (hlaw k)
  have hpref := poisson_prefix_sum_law P rate N hlaw hind
  have hr := poisson_prefix_rate_diverges rate hdiv
  have hrplus : Tendsto
      (fun n : Nat => ((∑ k ∈ Finset.range (n + 1), rate k) : Real))
      atTop atTop := by
    exact hr.comp (Filter.tendsto_add_atTop_nat 1)
  have hzero (m : Nat) :
      P {w | (∑' k, ((N k w : Nat) : ENNReal)) ≤ (m : ENNReal)} = 0 := by
    apply measure_null_of_upper_bounds_tendsto_zero P
      {w | (∑' k, ((N k w : Nat) : ENNReal)) ≤ (m : ENNReal)}
      (fun n => (poissonMeasure
        (∑ k ∈ Finset.range (n + 1), rate k)) (Set.Iic m))
    · intro n
      calc
        P {w | (∑' k, ((N k w : Nat) : ENNReal)) ≤ (m : ENNReal)} ≤
          P {w | (∑ k ∈ Finset.range (n + 1), N k w) ≤ m} :=
            total_count_event_measure_le_prefix P N n m
        _ = (poissonMeasure
            (∑ k ∈ Finset.range (n + 1), rate k)) (Set.Iic m) :=
              poisson_prefix_bounded_event_probability P rate N hm hpref n m
    · have hrateCast : Tendsto
          (fun n : Nat => (((∑ k ∈ Finset.range (n + 1), rate k) : NNReal) : Real))
          atTop atTop := by
        simpa only [NNReal.coe_sum] using hrplus
      exact poisson_bounded_count_probability_tendsto_zero
        (fun n => ∑ k ∈ Finset.range (n + 1), rate k) hrateCast m
  exact ae_top_of_null_all_finite_bounds P
    (fun w => ∑' k, ((N k w : Nat) : ENNReal)) hzero
