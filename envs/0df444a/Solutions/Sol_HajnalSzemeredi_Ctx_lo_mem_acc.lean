-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.lo_mem_acc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:11.905088+00:00
-- url     : https://prove2.me/submissions/34767921-2e6c-4c22-9675-ba4a0f1788b8

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure

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
theorem _root_.solution (h : Ctx G S P c r s lo hi) : lo ∈ acc G S P c lo :=
  mem_filter.mpr ⟨h.near.lo_mem, ReflTransGen.refl⟩
end HajnalSzemeredi.Ctx
