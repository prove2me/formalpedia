-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.card_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:31.502299+00:00
-- url     : https://prove2.me/submissions/e70cfd23-8e15-4a56-b7a7-e4ff16b7ffa1

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_card_part
public import Theorems.Thm_HajnalSzemeredi_Ctx_acc_subset
public import Theorems.Thm_HajnalSzemeredi_Ctx_lo_mem_acc
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
theorem _root_.solution (h : Ctx G S P c r s lo hi) :
    (part S c (acc G S P c lo)).card + 1 = (acc G S P c lo).card * s := by
  rw [card_part, ← add_sum_erase _ _ h.lo_mem_acc]
  have hsum : ∑ i ∈ (acc G S P c lo).erase lo, (cls S c i).card =
      ∑ _i ∈ (acc G S P c lo).erase lo, s := by
    refine sum_congr rfl fun i hi' => ?_
    obtain ⟨hil, hiA⟩ := mem_erase.mp hi'
    refine h.near.card i (acc_subset hiA) hil ?_
    rintro rfl
    exact h.hi_not hiA
  rw [hsum, sum_const, smul_eq_mul, card_erase_of_mem h.lo_mem_acc]
  have hlo := h.near.card_lo
  have : 1 ≤ (acc G S P c lo).card := card_pos.mpr ⟨lo, h.lo_mem_acc⟩
  obtain ⟨k, hk⟩ : ∃ k, (acc G S P c lo).card = k + 1 := ⟨_, (Nat.sub_add_cancel this).symm⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  rw [← hlo]
  ring
end HajnalSzemeredi.Ctx
