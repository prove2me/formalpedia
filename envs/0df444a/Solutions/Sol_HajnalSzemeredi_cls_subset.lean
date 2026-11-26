-- Prove2me | solution 1 for HajnalSzemeredi.cls_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:09.9006+00:00
-- url     : https://prove2.me/submissions/bccf5095-7a99-4ee8-9d54-6218824f95ca

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_HajnalSzemeredi_Defs

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace HajnalSzemeredi
theorem _root_.solution (S : Finset V) (c : V → ℕ) (i : ℕ) : cls S c i ⊆ S := filter_subset _ _
end HajnalSzemeredi
