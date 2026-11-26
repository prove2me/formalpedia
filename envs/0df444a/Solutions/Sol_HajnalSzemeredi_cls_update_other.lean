-- Prove2me | solution 1 for HajnalSzemeredi.cls_update_other
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:23.573177+00:00
-- url     : https://prove2.me/submissions/2ee1d21b-9ade-415e-b1b2-9564271dd8ec

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
theorem _root_.solution {k : ℕ} (hk : k ≠ j) (hk' : k ≠ c v) :
    cls S (Function.update c v j) k = cls S c k := by
  ext w
  by_cases hw : w = v
  · subst hw; simp [Ne.symm hk, Ne.symm hk']
  · simp [hw]
end HajnalSzemeredi
