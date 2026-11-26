-- Prove2me | solution 1 for HajnalSzemeredi.exists_step_avoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:35.01746+00:00
-- url     : https://prove2.me/submissions/89ef25c6-68c8-4350-b107-b56ab1d26a73

module
public import Mathlib.Logic.Relation
public import Definitions.Def_HajnalSzemeredi_Reach

set_option autoImplicit true
@[expose] public section
public section
open HajnalSzemeredi
open Relation
variable {α : Type*}
namespace HajnalSzemeredi
theorem _root_.solution {R : α → α → Prop} {x z : α} (h : ReflTransGen R x z) (hxz : x ≠ z) :
    ∃ j, R x j ∧ j ≠ x ∧ ReflTransGen (fun a b => R a b ∧ a ≠ x ∧ b ≠ x) j z := by
  induction h with
  | refl => exact absurd rfl hxz
  | @tail a b hxa hab ih =>
    by_cases ha : a = x
    · subst ha
      exact ⟨b, hab, Ne.symm hxz, ReflTransGen.refl⟩
    · obtain ⟨j, hj, hjx, hjb⟩ := ih (Ne.symm ha)
      exact ⟨j, hj, hjx, hjb.tail ⟨hab, ha, Ne.symm hxz⟩⟩
end HajnalSzemeredi
