-- Prove2me | solution 1 for HajnalSzemeredi.cls_update_old
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:02.868225+00:00
-- url     : https://prove2.me/submissions/8b63587d-42d2-42d1-9e9c-cec6b8a71676

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_HajnalSzemeredi_Defs
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
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
    cls S (Function.update c v j) (c v) = (cls S c (c v)).erase v := by
  ext w
  by_cases hw : w = v
  · subst hw; simp [Ne.symm hj]
  · simp [hw]
end HajnalSzemeredi
