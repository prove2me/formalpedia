-- Prove2me | solution 1 for HajnalSzemeredi.bminus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:05.340797+00:00
-- url     : https://prove2.me/submissions/dc29878a-a36f-46aa-807c-516bb72436ca

module
public import Definitions.Def_HajnalSzemeredi_Cases
public import Definitions.Def_HajnalSzemeredi_Main
public import Theorems.Thm_HajnalSzemeredi_CountHyp_deg_B
public import Theorems.Thm_HajnalSzemeredi_Ctx_card_B
public import Theorems.Thm_HajnalSzemeredi_Ctx_h21
public import Theorems.Thm_HajnalSzemeredi_Ctx_hi_mem_B
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
namespace HajnalSzemeredi
theorem _root_.solution {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ} {TU : Finset ℕ}
    (h : Ctx G S P c r s lo hi)
    (hch : CountHyp G S c (acc G S P c lo) (P \ acc G S P c lo) TU r s) {y₁ : V}
    (hy₁ : y₁ ∈ part S c (P \ acc G S P c lo)) :
    (part S c (P \ acc G S P c lo)).erase y₁ ⊆ S ∧
    edgeCount G ((part S c (P \ acc G S P c lo)).erase y₁) < edgeCount G S ∧
    ((part S c (P \ acc G S P c lo)).erase y₁).card =
      s * ((P \ acc G S P c lo).card - 1 + 1) ∧
    DegLe G ((part S c (P \ acc G S P c lo)).erase y₁) ((P \ acc G S P c lo).card - 1) := by
  set PB := P \ acc G S P c lo
  set B := part S c PB
  have hBS : B.erase y₁ ⊆ S := (erase_subset _ _).trans (filter_subset _ _)
  have hPB : 1 ≤ PB.card := card_pos.mpr ⟨hi, h.hi_mem_B⟩
  have hs : 1 ≤ s := by have := h.near.card_lo; omega
  have hcard : (B.erase y₁).card = s * (PB.card - 1 + 1) := by
    have hB : B.card = PB.card * s + 1 := h.card_B
    rw [card_erase_of_mem hy₁, hB, Nat.sub_add_cancel hPB, Nat.add_sub_cancel, Nat.mul_comm]
  refine ⟨hBS, ?_, hcard, ?_⟩
  · -- hay una arista entre `B⁻` y la clase `lo`
    obtain ⟨y, hy⟩ : (B.erase y₁).Nonempty := by
      rw [← card_pos, hcard]; exact Nat.mul_pos hs (Nat.succ_pos _)
    have hyB := (mem_erase.mp hy).2
    obtain ⟨w, hw⟩ := h.h21 hyB h.lo_mem_acc
    rw [nIn, mem_inter, mem_nbr, mem_cls] at hw
    have hwB : w ∉ B.erase y₁ := by
      intro hwB
      have := (mem_filter.mp (mem_erase.mp hwB).2).2
      rw [hw.2.2] at this
      exact (mem_sdiff.mp this).2 h.lo_mem_acc
    apply card_lt_card
    refine ⟨fun p hp => ?_, fun hsub => ?_⟩
    · obtain ⟨hp, hadj⟩ := mem_filter.mp hp
      obtain ⟨h1, h2, h3⟩ := mem_offDiag.mp hp
      exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨hBS h1, hBS h2, h3⟩, hadj⟩
    · have hyw : (y, w) ∈ (S.offDiag.filter fun p => G.Adj p.1 p.2) :=
        mem_filter.mpr ⟨mem_offDiag.mpr ⟨hBS hy, hw.1.1, hw.1.2.ne⟩, hw.1.2⟩
      exact hwB (mem_offDiag.mp (mem_filter.mp (hsub hyw)).1).2.1
  · intro y hy
    have hyB := (mem_erase.mp hy).2
    have h1 : (nbr G B y).card + 1 ≤ PB.card := hch.deg_B hyB
    have h2 : (nbr G (B.erase y₁) y).card ≤ (nbr G B y).card :=
      card_le_card fun w hw => mem_nbr.mpr ⟨(mem_erase.mp (mem_nbr.mp hw).1).2, (mem_nbr.mp hw).2⟩
    omega
end HajnalSzemeredi
