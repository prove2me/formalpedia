-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.card_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:26.589833+00:00
-- url     : https://prove2.me/submissions/b9c01de9-5d05-4b65-9aa3-f57559151f5f

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_card_part
public import Theorems.Thm_HajnalSzemeredi_Ctx_lo_mem_acc
public import Theorems.Thm_HajnalSzemeredi_Ctx_hi_mem_B
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
    (part S c (P \ acc G S P c lo)).card = (P \ acc G S P c lo).card * s + 1 := by
  rw [card_part, ← add_sum_erase _ _ h.hi_mem_B]
  have hsum : ∑ i ∈ (P \ acc G S P c lo).erase hi, (cls S c i).card =
      ∑ _i ∈ (P \ acc G S P c lo).erase hi, s := by
    refine sum_congr rfl fun i hi' => ?_
    obtain ⟨hih, hiB⟩ := mem_erase.mp hi'
    obtain ⟨hiP, hiA⟩ := mem_sdiff.mp hiB
    refine h.near.card i hiP ?_ hih
    rintro rfl
    exact hiA h.lo_mem_acc
  rw [hsum, sum_const, smul_eq_mul, card_erase_of_mem h.hi_mem_B, h.near.card_hi]
  have : 1 ≤ (P \ acc G S P c lo).card := card_pos.mpr ⟨hi, h.hi_mem_B⟩
  obtain ⟨k, hk⟩ : ∃ k, (P \ acc G S P c lo).card = k + 1 := ⟨_, (Nat.sub_add_cancel this).symm⟩
  rw [hk]
  simp only [Nat.add_sub_cancel]
  ring
end HajnalSzemeredi.Ctx
