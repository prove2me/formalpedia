-- Prove2me | solution 1 for IntMul.Kappa.controlled_shift_permutation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T21:57:29.88274+00:00
-- url     : https://prove2.me/submissions/bc713059-c88b-4853-916f-868419f004d4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (C : Type) (Q : ℕ) (a : C → ZMod Q) :
    Function.Bijective
      (fun p : C × ZMod Q => (p.1, p.2 + a p.1)) ∧
    (∀ p : C × ZMod Q,
      (fun t : C × ZMod Q => (t.1, t.2 - a t.1))
        ((fun t : C × ZMod Q => (t.1, t.2 + a t.1)) p) = p) := by
  let f : C × ZMod Q → C × ZMod Q :=
    fun p => (p.1, p.2 + a p.1)
  let g : C × ZMod Q → C × ZMod Q :=
    fun p => (p.1, p.2 - a p.1)
  have hleft : Function.LeftInverse g f := by
    intro ⟨c, y⟩
    simp [f, g]
  have hright : Function.RightInverse g f := by
    intro ⟨c, y⟩
    simp [f, g]
  constructor
  · exact ⟨hleft.injective, hright.surjective⟩
  · exact hleft
