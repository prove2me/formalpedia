-- Prove2me | solution 1 for HatAffineGeneral.extends_iff_coverable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:07:06.836613+00:00
-- url     : https://prove2.me/submissions/5a8a8b7f-c3db-48e2-a2ca-fe165f3ee1a6

import Mathlib
import Definitions.Def_HatAffineGeneral_Discovery

set_option autoImplicit true
open scoped BigOperators
open HatAffineGeneral
universe u v w
namespace HatAffineGeneral
theorem _root_.solution
    {K : Type u} {I : Type v} {J : Type w}
    (F : (J → K) → I → K) :
    Extends F ↔
      ∀ x : I → K, ∃ g : J → K, Covers g (BadSet F x) := by
  constructor
  · rintro ⟨G, hG⟩ x
    refine ⟨G x, ?_⟩
    intro y hy
    rcases hG x y with hleft | hright
    · obtain ⟨i, hi⟩ := hleft
      exact (hy i hi).elim
    · obtain ⟨j, hj⟩ := hright
      exact ⟨j, hj.symm⟩
  · intro h
    classical
    choose G hG using h
    refine ⟨G, ?_⟩
    intro x y
    by_cases hx : ∃ i, F y i = x i
    · exact Or.inl hx
    · apply Or.inr
      have hy : y ∈ BadSet F x := by
        intro i hi
        exact hx ⟨i, hi⟩
      obtain ⟨j, hj⟩ := hG x y hy
      exact ⟨j, hj.symm⟩
end HatAffineGeneral
