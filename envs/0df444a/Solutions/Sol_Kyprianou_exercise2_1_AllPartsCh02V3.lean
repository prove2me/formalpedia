-- Prove2me | solution 1 for Kyprianou.exercise2_1_AllPartsCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:55:43.092194+00:00
-- url     : https://prove2.me/submissions/4784b7d2-5ce7-4d07-b22b-7a91c96e7119

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_aemeasurable_of_poisson_law
import Theorems.Thm_Kyprianou_ProofPreparation_finite_poisson_count_real_total_hasLaw
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_count_sum_ae_finite_of_summable_rates
import Theorems.Thm_Kyprianou_ProofPreparation_exercise2_1_infinite_rate_divergence
import Theorems.Thm_Kyprianou_ProofPreparation_finite_ennreal_poisson_law_of_real_cast
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℕ → ℝ≥0) (N : ℕ → Ω → ℕ)
    (hlaw : ∀ k, P.map (N k) = ProbabilityTheory.poissonMeasure (rate k))
    (hind : ProbabilityTheory.iIndepFun N P) :
    (((∑' k, (rate k : ℝ≥0∞)) < ⊤) →
       (P.map (fun ω => ∑' k, ((N k ω : ℕ) : ℝ≥0∞)) =
          (ProbabilityTheory.poissonMeasure
            ((∑' k, (rate k : ℝ≥0∞)).toNNReal)).map
              (Nat.cast : ℕ → ENNReal)) ∧
       (∀ᵐ ω ∂P, (∑' k, ((N k ω : ℕ) : ℝ≥0∞)) < ⊤)) ∧
    (((∑' k, (rate k : ℝ≥0∞)) = ⊤) →
       ∀ᵐ ω ∂P, (∑' k, ((N k ω : ℕ) : ℝ≥0∞)) = ⊤)
      := by
  constructor
  · intro hfinite
    have hs : Summable rate :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp (ne_of_lt hfinite)
    have hcount :
        ∀ᵐ ω ∂P, (∑' k, ((N k ω : ℕ) : ENNReal)) < ⊤ :=
      Kyprianou.ProofPreparation.poisson_count_sum_ae_finite_of_summable_rates
        P rate N hlaw hfinite
    have hmeas : AEMeasurable
        (fun ω : Ω => ∑' k, ((N k ω : ℕ) : ENNReal)) P := by
      apply AEMeasurable.ennreal_tsum
      intro k
      have hcast : Measurable (fun n : ℕ => (n : ENNReal)) := by fun_prop
      exact hcast.comp_aemeasurable
        (Kyprianou.ProofPreparation.aemeasurable_of_poisson_law P (rate k) (N k) (hlaw k))
    constructor
    · apply Kyprianou.ProofPreparation.finite_ennreal_poisson_law_of_real_cast
        P (fun ω : Ω => ∑' k, ((N k ω : ℕ) : ENNReal))
        ((∑' k, (rate k : ENNReal)).toNNReal) hmeas hcount
      exact Kyprianou.ProofPreparation.finite_poisson_count_real_total_hasLaw
        P rate N hlaw hind hs hcount
    · exact hcount
  · intro hdiv
    exact Kyprianou.ProofPreparation.exercise2_1_infinite_rate_divergence
      P rate N hlaw hind hdiv
