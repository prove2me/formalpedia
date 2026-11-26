-- Prove2me | solution 1 for HajnalSzemeredi.rtgMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:52.123545+00:00
-- url     : https://prove2.me/submissions/325dcac5-91d5-468b-abb0-d0028c1a4df8

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
theorem _root_.solution {α : Type*} {R R' : α → α → Prop} {a b : α} (h : ReflTransGen R a b)
    (hR : ∀ x y, R x y → R' x y) : ReflTransGen R' a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hxy ih => exact ih.tail (hR _ _ hxy)
end HajnalSzemeredi
