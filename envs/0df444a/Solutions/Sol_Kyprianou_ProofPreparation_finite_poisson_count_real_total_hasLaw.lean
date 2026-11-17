-- Prove2me | solution 1 for Kyprianou.ProofPreparation.finite_poisson_count_real_total_hasLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:57:26.811199+00:00
-- url     : https://prove2.me/submissions/7ea3a6e2-0113-4b6f-97e7-6f7a8bd38b28

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_aemeasurable_of_poisson_law
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prefix_distribution_to_poisson_rate
import Theorems.Thm_Kyprianou_ProofPreparation_finite_poisson_prefix_real_shift_tendstoInDistribution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P)
    (hsum : Summable rate)
    (hfinite : ∀ᵐ w ∂P,
      (∑' k, ((N k w : Nat) : ENNReal)) < ⊤) :
    P.map (fun w : Omega =>
      ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal) =
      (poissonMeasure ((∑' k, (rate k : ENNReal)).toNNReal)).map
        (Nat.cast : Nat -> Real) := by
  have hm : forall k, AEMeasurable (N k) P :=
    fun k => aemeasurable_of_poisson_law P (rate k) (N k) (hlaw k)
  have hpath :=
    finite_poisson_prefix_real_shift_tendstoInDistribution
      P N hm hfinite
  have hlawlimit :=
    poisson_prefix_distribution_to_poisson_rate P rate N hlaw hind hsum
  exact tendstoInDistribution_unique _ hpath hlawlimit
