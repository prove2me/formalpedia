-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_count_sum_ae_finite_of_summable_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:48:56.62967+00:00
-- url     : https://prove2.me/submissions/ef62c964-d1ca-40f4-a4ae-337917262a36

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_aemeasurable_of_poisson_law
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_marginal_lintegral
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
    (P : Measure Omega)
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hfinite : (∑' k, (rate k : ENNReal)) < ⊤) :
    ∀ᵐ w ∂P, (∑' k, ((N k w : Nat) : ENNReal)) < ⊤ := by
  have hm : forall k, AEMeasurable
      (fun w : Omega => ((N k w : Nat) : ENNReal)) P := by
    intro k
    have hcast : Measurable (fun n : Nat => (n : ENNReal)) := by fun_prop
    exact hcast.comp_aemeasurable
      (aemeasurable_of_poisson_law P (rate k) (N k) (hlaw k))
  have hmoment :
      (∫⁻ w, (∑' k, ((N k w : Nat) : ENNReal)) ∂P) =
        (∑' k, (rate k : ENNReal)) := by
    rw [lintegral_tsum hm]
    congr 1
    funext k
    exact poisson_marginal_lintegral P (N k) (rate k) (hlaw k)
  have htot :
      AEMeasurable (fun w : Omega =>
        (∑' k, ((N k w : Nat) : ENNReal))) P :=
    AEMeasurable.ennreal_tsum hm
  exact ae_lt_top' htot (by rw [hmoment]; exact ne_of_lt hfinite)
