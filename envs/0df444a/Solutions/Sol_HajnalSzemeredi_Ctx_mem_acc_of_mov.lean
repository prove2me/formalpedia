-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.mem_acc_of_mov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:48.576368+00:00
-- url     : https://prove2.me/submissions/434a866a-971d-4044-8c69-5ae4d973f271

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_mem_cls
attribute [local simp] HajnalSzemeredi.mem_cls



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
theorem _root_.solution (h : Ctx G S P c r s lo hi) {a b : ℕ} (hab : Mov G S c a b)
    (hb : b ∈ acc G S P c lo) : a ∈ acc G S P c lo := by
  obtain ⟨v, hv, -⟩ := id hab
  rw [mem_cls] at hv
  exact mem_filter.mpr ⟨hv.2 ▸ h.near.into v hv.1, ReflTransGen.head hab (mem_filter.mp hb).2⟩
end HajnalSzemeredi.Ctx
