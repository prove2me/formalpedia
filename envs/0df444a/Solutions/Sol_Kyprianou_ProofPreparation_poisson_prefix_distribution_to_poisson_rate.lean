-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prefix_distribution_to_poisson_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:56:50.861194+00:00
-- url     : https://prove2.me/submissions/db81d40f-6db8-45de-b4da-90bc5ff09e03

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_aemeasurable_of_poisson_law
import Theorems.Thm_Kyprianou_ProofPreparation_finite_prefix_real_poisson_law
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_charfun_continuous_in_rate
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prefix_rates_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

namespace Kyprianou.ProofPreparation
private def realPoissonProbabilityPrivate (r : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨(poissonMeasure r).map (Nat.cast : ℕ → ℝ), inferInstance⟩

/-- Weak continuity of the Poisson law under a converging rate. -/
private theorem poisson_measure_weakly_continuous_private
    (rate : ℕ → ℝ≥0) (r : ℝ≥0)
    (hrate : Tendsto rate atTop (𝓝 r)) :
    Tendsto (fun n : ℕ => realPoissonProbabilityPrivate (rate n))
      atTop (𝓝 (realPoissonProbabilityPrivate r)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  change Tendsto
    (fun n : ℕ => charFun ((poissonMeasure (rate n)).map
      (Nat.cast : ℕ → ℝ)) t) atTop
      (𝓝 (charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) t))
  exact poisson_charfun_continuous_in_rate rate r hrate t

end Kyprianou.ProofPreparation

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P) (hsum : Summable rate) :
    TendstoInDistribution
      (fun n (w : Omega) =>
        (((∑ k ∈ Finset.range (n + 1), N k w) : Nat) : Real))
      atTop (Nat.cast : Nat -> Real) (fun _ => P)
      (poissonMeasure ((∑' k, (rate k : ENNReal)).toNNReal)) := by
  have hm : forall k, AEMeasurable (N k) P :=
    fun k => aemeasurable_of_poisson_law P (rate k) (N k) (hlaw k)
  have hpref (n : Nat) : AEMeasurable
      (fun w : Omega => (((∑ k ∈ Finset.range (n + 1), N k w) : Nat) : Real)) P := by
    have hsummeas : AEMeasurable
        (fun w : Omega => ∑ k ∈ Finset.range (n + 1), N k w) P := by
      have heq : (∑ k ∈ Finset.range (n + 1), N k) =
          (fun w : Omega => ∑ k ∈ Finset.range (n + 1), N k w) := by
        funext w
        simp only [Finset.sum_apply]
      rw [← heq]
      exact Finset.aemeasurable_sum (Finset.range (n + 1))
        (fun k hk => hm k)
    have hcast : Measurable (fun k : Nat => (k : Real)) := by fun_prop
    exact hcast.comp_aemeasurable hsummeas
  have hr : Tendsto
      (fun n : Nat => ∑ k ∈ Finset.range (n + 1), rate k)
      atTop (𝓝 ((∑' k, (rate k : ENNReal)).toNNReal)) :=
    (poisson_prefix_rates_tendsto rate hsum).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hweak := poisson_measure_weakly_continuous_private
      (fun n : Nat => ∑ k ∈ Finset.range (n + 1), rate k)
      ((∑' k, (rate k : ENNReal)).toNNReal) hr
  apply TendstoInDistribution.mk hpref
    (by fun_prop : AEMeasurable (Nat.cast : Nat -> Real)
       (poissonMeasure ((∑' k, (rate k : ENNReal)).toNNReal)))
  have heq (n : Nat) :
      (⟨P.map
          (fun w : Omega =>
            (((∑ k ∈ Finset.range (n + 1), N k w) : Nat) : Real)),
          (by rw [finite_prefix_real_poisson_law P rate N hlaw hind n]
              infer_instance)⟩ : ProbabilityMeasure Real) =
      realPoissonProbabilityPrivate
        (∑ k ∈ Finset.range (n + 1), rate k) := by
    apply Subtype.ext
    exact finite_prefix_real_poisson_law P rate N hlaw hind n
  simpa only [heq, realPoissonProbabilityPrivate] using hweak
