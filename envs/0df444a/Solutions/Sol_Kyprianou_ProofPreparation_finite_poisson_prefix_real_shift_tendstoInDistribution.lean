-- Prove2me | solution 1 for Kyprianou.ProofPreparation.finite_poisson_prefix_real_shift_tendstoInDistribution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:58:02.624358+00:00
-- url     : https://prove2.me/submissions/fc3e02c8-22de-43b7-8ac3-3951703f189f

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_finite_poisson_prefix_real_tendstoInDistribution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (N : Nat -> Omega -> Nat)
    (hN : forall k, AEMeasurable (N k) P)
    (hfinite : ∀ᵐ w ∂P,
       (∑' k, ((N k w : Nat) : ENNReal)) < ⊤) :
    TendstoInDistribution
      (fun n (w : Omega) =>
        (((∑ k ∈ Finset.range (n + 1), N k w) : Nat) : Real))
      atTop (fun w : Omega =>
        ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal)
      (fun _ => P) P := by
  have hbase :=
    finite_poisson_prefix_real_tendstoInDistribution P N hN hfinite
  refine TendstoInDistribution.mk
    (fun n => hbase.forall_aemeasurable (n + 1))
    hbase.aemeasurable_limit ?_
  have hshift := hbase.tendsto.comp (Filter.tendsto_add_atTop_nat 1)
  refine hshift.congr' ?_
  apply Filter.Eventually.of_forall
  intro n
  apply Subtype.ext
  rfl
