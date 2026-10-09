-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_optimal_of_conditional_concavity_and_base
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:03:03.924722+00:00
-- url     : https://prove2.me/submissions/c6c9cfa2-d962-4f99-b44d-bdf64591b4be

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_corollary1_integrate_conditional_concavity
import Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_of_prefix_concavity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p)
    (hbase : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p 1))
    (hcond : ∀ k, 1 ≤ k → ∀ y, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) :
    IsOptimal P X f p := by
  have hconc : ∀ k, 1 ≤ k →
      ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k) := by
    intro k hk
    by_cases h1 : k = 1
    · subst k
      exact hbase
    · have hkm : 1 ≤ k - 1 := by omega
      have hkval : (k - 1) + 1 = k := by omega
      have hpoint := corollary1_integrate_conditional_concavity
        P X f p hM hp (k - 1) (hcond (k - 1) hkm)
      simpa only [hkval] using hpoint
  exact theorem1_global_optimality_of_prefix_concavity
    P X f p hM hp h20 hconc
