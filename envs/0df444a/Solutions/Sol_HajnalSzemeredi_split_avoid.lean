-- Prove2me | solution 1 for HajnalSzemeredi.split_avoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:40.83411+00:00
-- url     : https://prove2.me/submissions/50129a60-2ebd-4021-9b61-60fce703010d

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace HajnalSzemeredi
theorem _root_.solution {α : Type*} {R : α → α → Prop} {x z : α} :
    ∀ {a}, ReflTransGen R a z → a ≠ x →
      ReflTransGen (fun u v => R u v ∧ u ≠ x ∧ v ≠ x) a z ∨ ReflTransGen R x z := by
  intro a h
  induction h using ReflTransGen.head_induction_on with
  | refl => exact fun _ => Or.inl ReflTransGen.refl
  | head hab hbz ih =>
    rename_i a b
    intro hax
    by_cases hbx : b = x
    · subst hbx; exact Or.inr hbz
    · rcases ih hbx with h | h
      · exact Or.inl (ReflTransGen.head ⟨hab, hax, hbx⟩ h)
      · exact Or.inr h
end HajnalSzemeredi
