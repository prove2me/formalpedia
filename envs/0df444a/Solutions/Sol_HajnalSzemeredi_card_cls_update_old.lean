-- Prove2me | solution 1 for HajnalSzemeredi.card_cls_update_old
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:31.588241+00:00
-- url     : https://prove2.me/submissions/52114524-66cb-4fa7-8b8a-3e1a1c76b65f

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_HajnalSzemeredi_Defs
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
public import Theorems.Thm_HajnalSzemeredi_cls_update_old
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} (G : SimpleGraph V)
variable {G}
variable {S : Finset V} {c : V → ℕ} {v : V} {j : ℕ}
namespace HajnalSzemeredi
theorem _root_.solution (hv : v ∈ S) (hj : c v ≠ j) :
    (cls S (Function.update c v j) (c v)).card + 1 = (cls S c (c v)).card := by
  rw [cls_update_old hv hj, card_erase_add_one]
  simp [hv]
end HajnalSzemeredi
