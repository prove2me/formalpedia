-- Prove2me | solution 1 for Kyprianou.ProofPreparation.finite_poisson_prefix_real_tendstoInDistribution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:48:45.899612+00:00
-- url     : https://prove2.me/submissions/bdacd214-0e18-44a3-b110-e30409baefa2

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_ae_poisson_prefix_real_tendsto_finite_total
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
    (N : Nat -> Omega -> Nat)
    (hN : forall k, AEMeasurable (N k) P)
    (hfinite : ∀ᵐ w ∂P,
       (∑' k, ((N k w : Nat) : ENNReal)) < ⊤) :
    TendstoInDistribution
      (fun n (w : Omega) =>
        (((∑ k ∈ Finset.range n, N k w) : Nat) : Real))
      atTop (fun w : Omega =>
        ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal)
      (fun _ => P) P := by
  have hm : forall k, AEMeasurable
      (fun w : Omega => ((N k w : Nat) : Real)) P := by
    intro k
    have hcast : Measurable (fun k : Nat => (k : Real)) := by fun_prop
    exact hcast.comp_aemeasurable (hN k)
  have hpref (n : Nat) : AEMeasurable
      (fun w : Omega =>
        (((∑ k ∈ Finset.range n, N k w) : Nat) : Real)) P := by
    have heq :
      (∑ k ∈ Finset.range n,
        fun w : Omega => ((N k w : Nat) : Real)) =
        (fun w : Omega =>
          (((∑ k ∈ Finset.range n, N k w) : Nat) : Real)) := by
      funext w
      simp only [Finset.sum_apply, Nat.cast_sum]
    rw [← heq]
    exact Finset.aemeasurable_sum (Finset.range n)
      (fun k hk => hm k)
  have htotal : AEMeasurable
      (fun w : Omega =>
        ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal) P := by
    have hcast : Measurable (fun x : ENNReal => x.toReal) := by fun_prop
    have hcounts (k : Nat) : AEMeasurable
        (fun w : Omega => ((N k w : Nat) : ENNReal)) P := by
      have hc : Measurable (fun j : Nat => (j : ENNReal)) := by fun_prop
      exact hc.comp_aemeasurable (hN k)
    exact hcast.comp_aemeasurable (AEMeasurable.ennreal_tsum hcounts)
  apply tendstoInDistribution_of_ae_tendsto
  · exact hpref
  · exact htotal
  · exact ae_poisson_prefix_real_tendsto_finite_total P N hfinite
