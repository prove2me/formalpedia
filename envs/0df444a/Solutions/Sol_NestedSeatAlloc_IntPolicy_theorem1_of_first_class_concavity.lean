-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_of_first_class_concavity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:37:32.079688+00:00
-- url     : https://prove2.me/submissions/b0cc0f15-02fa-4efd-a2fd-f539166707c4

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_corollary1_conditional_revenue_concave
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
    (hbase : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p 1)) :
    (∀ k, 1 ≤ k → ∀ y, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) ∧
      IsOptimal P X f p := by
  have hC : ∀ n : ℕ, ConcaveOn ℝ (Set.Ici 0)
      (expRevenue P X f p (n + 1)) := by
    intro n
    induction n with
    | zero =>
        exact hbase
    | succ n ih =>
        have hk : 1 ≤ n + 1 := by omega
        have hcond : ∀ y, 0 ≤ y →
            ConcaveOn ℝ (Set.Ici 0)
              (condRevenue P X f p ((n + 1) + 1) y) := by
          intro y hy
          exact corollary1_conditional_revenue_concave
            P X f p hM hp (n + 1) hk ih
              (h20 (n + 1) hk) y hy
        have hnext := corollary1_integrate_conditional_concavity
          P X f p hM hp (n + 1) hcond
        simpa only [Nat.succ_eq_add_one] using hnext
  have hall : ∀ k, 1 ≤ k →
      ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k) := by
    intro k hk
    have hidx : (k - 1) + 1 = k := by omega
    simpa only [hidx] using hC (k - 1)
  constructor
  · intro k hk y hy
    exact corollary1_conditional_revenue_concave
      P X f p hM hp k hk (hall k hk) (h20 k hk) y hy
  · exact theorem1_global_optimality_of_prefix_concavity
      P X f p hM hp h20 hall
