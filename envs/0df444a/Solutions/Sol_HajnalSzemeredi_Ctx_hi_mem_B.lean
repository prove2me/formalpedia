-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.hi_mem_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:50.258721+00:00
-- url     : https://prove2.me/submissions/ce56c5d1-44de-4a73-bc88-732ee3545cb9

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
theorem _root_.solution (h : Ctx G S P c r s lo hi) : hi ∈ P \ acc G S P c lo :=
  mem_sdiff.mpr ⟨h.near.hi_mem, h.hi_not⟩
end HajnalSzemeredi.Ctx
