-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.h21
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:29.266425+00:00
-- url     : https://prove2.me/submissions/e0da5119-61e3-474a-809a-b0869e4ae2c4

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_Ctx_mem_acc_of_mov
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
open HajnalSzemeredi.Ctx
variable {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ}
namespace HajnalSzemeredi.Ctx
theorem _root_.solution (h : Ctx G S P c r s lo hi) {y : V} (hy : y ∈ part S c (P \ acc G S P c lo))
    {X : ℕ} (hX : X ∈ acc G S P c lo) : (nIn G S c y X).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hy' := mem_filter.mp hy
  have hmov : Mov G S c (c y) X := by
    refine ⟨y, mem_cls.mpr ⟨hy'.1, rfl⟩, fun w hw hadj => ?_⟩
    have : w ∈ nIn G S c y X := mem_inter.mpr ⟨mem_nbr.mpr ⟨(mem_cls.mp hw).1, hadj⟩, hw⟩
    rw [hne] at this
    exact notMem_empty _ this
  exact (mem_sdiff.mp hy'.2).2 (h.mem_acc_of_mov hmov hX)
end HajnalSzemeredi.Ctx
