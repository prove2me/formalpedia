-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.clbi_affine_unit_propagation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T09:07:11.687475+00:00
-- url     : https://prove2.me/submissions/60834f40-0fba-457a-88ff-4d79405fdf52

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_affine_unit_propagation_zero
import Theorems.Thm_NestedSeatAlloc_IntPolicy_clbi_affine_unit_propagation_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hint : ∀ k ω, ∃ n : ℕ, X k ω = n) (k : ℕ) (p : ℕ → ℕ)
    (hunit : ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) k s = a + b * s) :
    ∀ m : ℕ, ∃ a b : ℝ,
      ∀ s ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1),
        expRevenue P X f (fun j => (p j : ℝ)) (k + 1) s = a + b * s := by
  by_cases hk : k = 0
  · subst k
    exact clbi_affine_unit_propagation_zero P X f hM hint p
  · exact clbi_affine_unit_propagation_pos P X f hM hint k
      (Nat.pos_of_ne_zero hk) p hunit
