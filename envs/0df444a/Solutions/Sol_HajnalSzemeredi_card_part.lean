-- Prove2me | solution 1 for HajnalSzemeredi.card_part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:45.73774+00:00
-- url     : https://prove2.me/submissions/a70879a1-5858-486b-9fd5-12d710756fdc

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_cls_disjoint
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace HajnalSzemeredi
theorem _root_.solution (S : Finset V) (c : V → ℕ) (Q : Finset ℕ) :
    (part S c Q).card = ∑ i ∈ Q, (cls S c i).card := by
  rw [← card_biUnion]
  · congr 1
    ext v
    simp [part, mem_cls, and_comm]
  · intro i _ j _ hij
    exact cls_disjoint hij
end HajnalSzemeredi
