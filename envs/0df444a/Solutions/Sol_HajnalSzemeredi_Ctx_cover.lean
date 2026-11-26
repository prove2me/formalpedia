-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:46.626694+00:00
-- url     : https://prove2.me/submissions/b34e5dd4-1574-4a99-97b5-98f26f3aae54

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_Ctx_acc_subset

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
open HajnalSzemeredi.Ctx
variable {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ}
namespace HajnalSzemeredi.Ctx
theorem _root_.solution (h : Ctx G S P c r s lo hi) :
    ∀ v ∈ S, c v ∈ acc G S P c lo ∪ (P \ acc G S P c lo) := by
  intro v hv
  rw [union_sdiff_of_subset acc_subset]
  exact h.near.into v hv
end HajnalSzemeredi.Ctx
