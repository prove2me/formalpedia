-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.three_branch_policy_dominance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:51:20.000616+00:00
-- url     : https://prove2.me/submissions/379dfd47-c605-4318-a67a-13a564765516

import Mathlib
import Theorems.Thm_NestedSeatAlloc_IntPolicy_three_branch_eq_clamped_allocation
import Theorems.Thm_NestedSeatAlloc_IntPolicy_clamped_surplus_dominance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution (gq gp : ℝ → ℝ) (c a b y s : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hy : 0 ≤ y) (hs : 0 ≤ s)
    (hdom : ∀ t, 0 ≤ t → gq t ≤ gp t)
    (hleft : ∀ u v, 0 ≤ u → u ≤ v → v ≤ a →
      gp u - c * u ≤ gp v - c * v)
    (hright : ∀ u v, a ≤ u → u ≤ v →
      gp v - c * v ≤ gp u - c * u) :
    (if s < b then gq s else if s < b + y then
      (s - b) * c + gq b else y * c + gq (s - y)) ≤
    (if s < a then gp s else if s < a + y then
      (s - a) * c + gp a else y * c + gp (s - y)) := by
  rw [three_branch_eq_clamped_allocation gq b c y s hy,
    three_branch_eq_clamped_allocation gp a c y s hy]
  exact clamped_surplus_dominance gq gp c a s y b ha hs hy hb
    hdom hleft hright
