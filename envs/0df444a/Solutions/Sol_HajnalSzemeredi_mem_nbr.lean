-- Prove2me | solution 1 for HajnalSzemeredi.mem_nbr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:44:55.597999+00:00
-- url     : https://prove2.me/submissions/8bc131be-f8cc-4943-b04f-f5976c7e6022

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_HajnalSzemeredi_Defs
public import Theorems.Thm_HajnalSzemeredi_mem_cls
attribute [local simp] HajnalSzemeredi.mem_cls

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace HajnalSzemeredi
theorem _root_.solution {S : Finset V} {v w : V} : w ∈ nbr G S v ↔ w ∈ S ∧ G.Adj v w := by
  simp [nbr]
end HajnalSzemeredi
