-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prefix_sum_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:47:52.630705+00:00
-- url     : https://prove2.me/submissions/37b9f891-e507-4c9c-ada5-4ae9f20d65a6

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_two_poisson_sum_hasLaw
import Theorems.Thm_Kyprianou_ProofPreparation_independent_prefix_sum_of_aemeasurable
import Theorems.Thm_Kyprianou_ProofPreparation_aemeasurable_of_poisson_law
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rate : ℕ → ℝ≥0) (N : ℕ → Ω → ℕ)
    (hlaw : ∀ k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P) :
    ∀ n : ℕ,
      P.map (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω) =
        poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k) := by
  have hN : ∀ k, AEMeasurable (N k) P :=
    fun k => aemeasurable_of_poisson_law P (rate k) (N k) (hlaw k)
  intro n
  induction n with
  | zero =>
      simpa using hlaw 0
  | succ n ih =>
      have hnot : n + 1 ∉ Finset.range (n + 1) := by simp
      have hi : IndepFun
          (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω) (N (n + 1)) P :=
        independent_prefix_sum_of_aemeasurable P N hind hN
          (Finset.range (n + 1)) (n + 1) hnot
      have hnew := two_poisson_sum_hasLaw P
        (∑ k ∈ Finset.range (n + 1), rate k) (rate (n + 1))
        (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω) (N (n + 1))
        ih (hlaw (n + 1)) hi
      simpa only [Finset.sum_range_succ, Nat.succ_eq_add_one] using hnew
