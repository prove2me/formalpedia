-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_with_nonnegative_first_fare
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:47:38.743986+00:00
-- url     : https://prove2.me/submissions/08991358-2a40-4868-bf2e-6255fbe99423

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_expRevenue_one_concave_nonneg_fare
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_of_first_class_concavity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p)
    (hf1 : 0 ≤ f 1) :
    (∀ k, 1 ≤ k → ∀ y, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) ∧
      IsOptimal P X f p := by
  exact theorem1_of_first_class_concavity P X f p hM hp h20
    (expRevenue_one_concave_nonneg_fare P X f p hM hp hf1)
