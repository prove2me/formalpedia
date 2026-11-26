-- Prove2me | solution 1 for HajnalSzemeredi.sum_card_cls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:23.292882+00:00
-- url     : https://prove2.me/submissions/8e6a1a5b-60cb-4295-bc70-ac153f00626b

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_HajnalSzemeredi_Defs
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
public import Theorems.Thm_HajnalSzemeredi_cls_disjoint
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
namespace HajnalSzemeredi
theorem _root_.solution {S : Finset V} {c : V → ℕ} {P : Finset ℕ} (h : Into S c P) :
    ∑ i ∈ P, (cls S c i).card = S.card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext v
    simp only [mem_biUnion, mem_cls]
    exact ⟨fun ⟨_, _, hv, _⟩ => hv, fun hv => ⟨c v, h v hv, hv, rfl⟩⟩
  · intro i _ j _ hij
    exact cls_disjoint hij
end HajnalSzemeredi
