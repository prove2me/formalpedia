-- Prove2me | solution 1 for HairerSPDE.exists_memLp_two_representer_of_finite_norm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T12:18:04.31713+00:00
-- url     : https://prove2.me/submissions/b2e1b22b-28d9-4aa1-9462-6ac7d6869c8b

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Theorems.Thm_HairerSPDE_evalAt_bounded_of_finite_cameronMartinNorm
import Theorems.Thm_HairerSPDE_exists_memLp_representer_of_bounded_eval

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

-- The remote wrapper looks up an unqualified top-level `solution`, so the
-- target namespace is opened rather than entered.
open HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (hh : cameronMartinNorm μ h ≠ ∞) :
    ∃ h' : B → ℝ, Measurable h' ∧ MemLp h' 2 μ ∧
      (∀ L : StrongDual ℝ B, ∫ x, h' x * L x ∂μ = L h) ∧
      (∀ g : B → ℝ, MemLp g 2 μ →
        (∀ L : StrongDual ℝ B, ∫ x, g x * L x ∂μ = 0) → ∫ x, h' x * g x ∂μ = 0) := by
  obtain ⟨C, hC0, hC⟩ := evalAt_bounded_of_finite_cameronMartinNorm μ hμ h hh
  exact exists_memLp_representer_of_bounded_eval μ hμ h C hC
