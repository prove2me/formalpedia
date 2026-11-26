-- Prove2me | solution 1 for HajnalSzemeredi.cls_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:44:59.671036+00:00
-- url     : https://prove2.me/submissions/b48045a2-fb59-4a20-a19a-dc6d5936757f

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
theorem _root_.solution {S : Finset V} {c : V → ℕ} {i j : ℕ} (h : i ≠ j) :
    Disjoint (cls S c i) (cls S c j) := by
  rw [Finset.disjoint_left]
  intro v hi hj
  rw [mem_cls] at hi hj
  exact h (hi.2.symm.trans hj.2)
end HajnalSzemeredi
