-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.dependent_choice_sequence
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:24:58.524721+00:00
-- url     : https://prove2.me/submissions/ac309cfc-8c0e-4ea7-b451-d35d3db4c5b4

import Mathlib
set_option autoImplicit false

theorem solution {α : Type*} (R : α → α → Prop) (a₀ : α)
    (hnext : ∀ a, ∃ b, R a b) :
    ∃ u : ℕ → α, u 0 = a₀ ∧ ∀ n, R (u n) (u (n + 1)) := by
  choose f hf using hnext
  refine ⟨fun n => f^[n] a₀, rfl, fun n => ?_⟩
  show R (f^[n] a₀) (f^[n + 1] a₀)
  rw [Function.iterate_succ_apply']
  exact hf _
