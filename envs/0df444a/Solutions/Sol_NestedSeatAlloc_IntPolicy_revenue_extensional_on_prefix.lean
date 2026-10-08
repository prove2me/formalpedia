-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.revenue_extensional_on_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T08:56:09.073989+00:00
-- url     : https://prove2.me/submissions/38952b93-abd0-4b2b-a691-cbb7eb79a47c

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution (f p x y : ℕ → ℝ) :
    ∀ k : ℕ, (∀ i ∈ Finset.Icc 1 k, x i = y i) →
      ∀ s : ℝ, revenue f p x k s = revenue f p y k s := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
      intro _ s
      simp [revenue]
  | one =>
      intro hxy s
      have h1 : x 1 = y 1 := hxy 1 (by simp)
      simp [revenue, h1]
  | more n ih0 ih1 =>
      intro hxy s
      have hnext : x (n + 2) = y (n + 2) := hxy (n + 2) (by simp)
      have hprefix : ∀ i ∈ Finset.Icc 1 (n + 1), x i = y i := by
        intro i hi
        apply hxy i
        rcases Finset.mem_Icc.mp hi with ⟨hlo, hhi⟩
        exact Finset.mem_Icc.mpr ⟨hlo, by omega⟩
      simp only [revenue, hnext]
      split_ifs <;> simp [ih1 hprefix]
