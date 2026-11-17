-- Prove2me | solution 1 for Kyprianou.Ch01.isPreBrownianReal_initial_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:20:56.15167+00:00
-- url     : https://prove2.me/submissions/c43284e2-8605-43a5-a389-01b49d5ff309

import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal X P) :
    ∀ᵐ ω ∂P, X 0 ω = 0 := by
  have hlaw := hB.hasLaw_eval 0
  rw [ProbabilityTheory.gaussianReal_zero_var] at hlaw
  exact hlaw.ae_eq_of_dirac
