-- Prove2me | solution 1 for Kyprianou.ProofPreparation.ae_poisson_prefix_real_tendsto_finite_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:47:53.024443+00:00
-- url     : https://prove2.me/submissions/f814720c-923b-4874-8a78-5b4864d7cff1

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_finite_nonzero_indices_of_finite_count_sum
import Theorems.Thm_Kyprianou_ProofPreparation_eventually_prefix_eq_tsum_of_finite_support
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
    (P : Measure Omega) (N : Nat -> Omega -> Nat)
    (hfinite : ∀ᵐ w ∂P,
        (∑' k, ((N k w : Nat) : ENNReal)) < ⊤) :
    ∀ᵐ w ∂P,
      Tendsto
        (fun n : Nat => (((∑ k ∈ Finset.range n, N k w) : Nat) : Real))
        atTop
        (𝓝 ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal) := by
  filter_upwards [hfinite] with w hw
  have hs : Set.Finite {k : Nat | N k w ≠ 0} :=
    finite_nonzero_indices_of_finite_count_sum (fun k => N k w) hw
  obtain ⟨n, hn⟩ :=
    eventually_prefix_eq_tsum_of_finite_support (fun k => N k w) hs
  have hevent :
      (fun m : Nat => (((∑ k ∈ Finset.range m, N k w) : Nat) : Real))
        =ᶠ[atTop]
      (fun _ : Nat =>
        ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal) := by
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    have hcast := congrArg ENNReal.toReal (hn m hm)
    have hreal :
        (((∑ k ∈ Finset.range m, N k w) : Nat) : Real) =
          ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal := by
      rw [ENNReal.toReal_sum (by intro k hk; simp)] at hcast
      simpa only [ENNReal.toReal_natCast, Nat.cast_sum] using hcast.symm
    exact hreal
  exact tendsto_const_nhds.congr' hevent.symm
