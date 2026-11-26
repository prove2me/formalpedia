-- Prove2me | solution 1 for HajnalSzemeredi.transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:39.662047+00:00
-- url     : https://prove2.me/submissions/923588c8-abb2-4487-9154-94b59e055b72

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
theorem _root_.solution {R R' : α → α → Prop} {x z : α} (h : ReflTransGen R x z)
    (hR : ∀ a b, R a b → b ≠ x → R' a b) : ReflTransGen R' x z := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail b c _ hab ih =>
    by_cases hc : c = x
    · subst hc; exact ReflTransGen.refl
    · exact ih.tail (hR _ _ hab hc)
end HajnalSzemeredi
