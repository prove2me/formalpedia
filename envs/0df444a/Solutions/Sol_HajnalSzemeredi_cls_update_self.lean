-- Prove2me | solution 1 for HajnalSzemeredi.cls_update_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:01.070801+00:00
-- url     : https://prove2.me/submissions/946044df-7760-4d03-90e0-32cb292544c3

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
theorem _root_.solution (hv : v ∈ S) :
    cls S (Function.update c v j) j = insert v (cls S c j) := by
  ext w
  by_cases hw : w = v
  · subst hw; simp [hv]
  · simp [hw]
end HajnalSzemeredi
