-- Prove2me | solution 1 for Kyprianou.ProofPreparation.finite_prefix_real_poisson_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:48:45.596124+00:00
-- url     : https://prove2.me/submissions/e1c6bf71-7271-4807-9c33-7f65521f1586

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_aemeasurable_of_poisson_law
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prefix_sum_law
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_law_map_real_cast
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
    (hind : iIndepFun N P) (n : Nat) :
    P.map (fun w : Omega =>
      (((∑ k ∈ Finset.range (n + 1), N k w) : Nat) : Real)) =
      (poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k)).map
        (Nat.cast : Nat -> Real) := by
  have hm : forall k, AEMeasurable (N k) P :=
    fun k => aemeasurable_of_poisson_law P (rate k) (N k) (hlaw k)
  have hpref : AEMeasurable
      (fun w : Omega => ∑ k ∈ Finset.range (n + 1), N k w) P := by
    have heq :
        (∑ k ∈ Finset.range (n + 1), N k) =
          (fun w : Omega => ∑ k ∈ Finset.range (n + 1), N k w) := by
      funext w
      simp only [Finset.sum_apply]
    rw [← heq]
    exact Finset.aemeasurable_sum (Finset.range (n + 1))
      (fun k hk => hm k)
  exact poisson_law_map_real_cast P
    (fun w : Omega => ∑ k ∈ Finset.range (n + 1), N k w)
    (∑ k ∈ Finset.range (n + 1), rate k)
    (poisson_prefix_sum_law P rate N hlaw hind n) hpref
