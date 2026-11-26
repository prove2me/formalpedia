-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.numClasses_eq_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:36.211596+00:00
-- url     : https://prove2.me/submissions/1b12ba98-127d-4fc9-89ca-23132ec65ba1

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (s : Setoid α) (p : α → Prop) (t : Setoid (Subtype p))
    (ht : ∀ a b : Subtype p, t a b ↔ s a b) (hout : ∀ a b, ¬ p a → s a b → a = b)
    [Finite α] :
    numClasses s = numClasses t + Nat.card {x // ¬ p x} := by
  classical
  let g : Quotient t ⊕ {x // ¬ p x} → Quotient s := fun
    | Sum.inl q => Quotient.lift (fun a : Subtype p => Quotient.mk s a.1)
        (fun a b hab => Quotient.sound ((ht a b).1 hab)) q
    | Sum.inr x => Quotient.mk s x.1
  have hg : Function.Bijective g := by
    constructor
    · rintro (q | x) (q' | x') h
      · induction q using Quotient.inductionOn with
        | h a =>
        induction q' using Quotient.inductionOn with
        | h b =>
        exact congrArg Sum.inl (Quotient.sound ((ht a b).2 (Quotient.exact h)))
      · induction q using Quotient.inductionOn with
        | h a =>
        have h' : s x'.1 a.1 := s.symm (Quotient.exact h)
        exact absurd (hout _ _ x'.2 h' ▸ a.2) x'.2
      · induction q' using Quotient.inductionOn with
        | h a =>
        have h' : s x.1 a.1 := Quotient.exact h
        exact absurd (hout _ _ x.2 h' ▸ a.2) x.2
      · have h' : s x.1 x'.1 := Quotient.exact h
        exact congrArg Sum.inr (Subtype.ext (hout _ _ x.2 h'))
    · intro q
      induction q using Quotient.inductionOn with
      | h a =>
      by_cases ha : p a
      · exact ⟨Sum.inl (Quotient.mk t ⟨a, ha⟩), rfl⟩
      · exact ⟨Sum.inr ⟨a, ha⟩, rfl⟩
  have := Fintype.ofFinite α
  have h1 := Nat.card_eq_of_bijective g hg
  rw [Nat.card_sum] at h1
  exact h1.symm
end LeanPool.K5MinorFreeChoosability
