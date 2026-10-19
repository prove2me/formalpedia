-- Prove2me | solution 1 for IntMul.Kappa.controlled_affine_unit_permutation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T21:58:16.762172+00:00
-- url     : https://prove2.me/submissions/fcac8332-021f-452b-adbf-c779efc2b2f0

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (C : Type) (Q : ℕ)
    (u : C → (ZMod Q)ˣ) (a : C → ZMod Q) :
    Function.Bijective
      (fun p : C × ZMod Q =>
        (p.1, (u p.1 : ZMod Q) * p.2 + a p.1)) := by
  let f : C × ZMod Q → C × ZMod Q :=
    fun p => (p.1, (u p.1 : ZMod Q) * p.2 + a p.1)
  let g : C × ZMod Q → C × ZMod Q :=
    fun p => (p.1, (((u p.1)⁻¹ : (ZMod Q)ˣ) : ZMod Q) * (p.2 - a p.1))
  have hleft : Function.LeftInverse g f := by
    intro ⟨c, y⟩
    simp [f, g, mul_assoc]
  have hright : Function.RightInverse g f := by
    intro ⟨c, y⟩
    simp [f, g, mul_add, mul_assoc]
  exact ⟨hleft.injective, hright.surjective⟩
