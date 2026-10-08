-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.theorem1_conditional_concavity_assembly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:18:33.748077+00:00
-- url     : https://prove2.me/submissions/f0c42bf6-8664-4336-b0b0-3b1f997dc9cf

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) (h20 : SubdiffCondition P X f p)
    (hbase : ∀ y, 0 ≤ y → ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p 1 y))
    (hstep : ∀ k y, 1 ≤ k → 0 ≤ y →
      InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)) →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p k y) →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) :
    ∀ k, 1 ≤ k → ∀ y, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y) := by
  intro k
  induction k with
  | zero =>
      intro hk
      exact (Nat.not_succ_le_zero 0 hk).elim
  | succ k ih =>
      intro hk y hy
      apply hstep (k + 1) y hk hy
      · exact h20 (k + 1) hk
      · by_cases hk0 : k = 0
        · subst k
          simpa using hbase y hy
        · exact ih (Nat.one_le_iff_ne_zero.mpr hk0) y hy
