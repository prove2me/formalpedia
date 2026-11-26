-- Prove2me | solution 1 for HajnalSzemeredi.card_cls_update_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:30.926853+00:00
-- url     : https://prove2.me/submissions/9a28a93f-98c2-49e2-8343-53e2b69f23fe

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_HajnalSzemeredi_Defs
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
public import Theorems.Thm_HajnalSzemeredi_cls_update_self
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
    (cls S (Function.update c v j) j).card = (cls S c j).card + 1 := by
  rw [cls_update_self hv, card_insert_of_notMem]
  simp [hj]
end HajnalSzemeredi
