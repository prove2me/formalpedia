-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.countHyp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:16.463704+00:00
-- url     : https://prove2.me/submissions/e219b5ab-8195-43ad-8b2f-66af222ca4d8

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_Ctx_acc_subset
public import Theorems.Thm_HajnalSzemeredi_Ctx_cover
public import Theorems.Thm_HajnalSzemeredi_Ctx_card_r
public import Theorems.Thm_HajnalSzemeredi_Ctx_h21
public import Theorems.Thm_HajnalSzemeredi_Ctx_card_B
public import Theorems.Thm_HajnalSzemeredi_Ctx_lo_notMem_T
public import Theorems.Thm_HajnalSzemeredi_Ctx_T_subset
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
theorem _root_.solution (h : Ctx G S P c r s lo hi) {U : ℕ} (hU : U ∈ acc G S P c lo)
    (hne : (T G S P c lo U).Nonempty)
    (hP2 : ∀ X ∈ T G S P c lo U, ∀ Y ∈ acc G S P c lo, Y ∉ T G S P c lo U → Y ≠ U →
      ¬ Mov G S c X Y) :
    CountHyp G S c (acc G S P c lo) (P \ acc G S P c lo) (T G S P c lo U) r s := by
  refine ⟨disjoint_sdiff, h.cover, fun W hW => (mem_erase.mp (T_subset U hW)).2, hne,
    h.card_r, h.deg, ?_, h.card_B, fun y hy X hX => h.h21 hy hX, ?_⟩
  · intro W hW
    have hWacc := (mem_erase.mp (T_subset U hW)).2
    refine h.near.card W (acc_subset hWacc) ?_ ?_
    · rintro rfl; exact lo_notMem_T _ hW
    · rintro rfl; exact h.hi_not hWacc
  · intro x hx hxT
    set Q := (acc G S P c lo \ T G S P c lo U).erase U
    have hQ : Q ⊆ (nbr G (part S c (acc G S P c lo)) x).image c := by
      intro Y hY
      obtain ⟨hYU, hY'⟩ := mem_erase.mp hY
      obtain ⟨hYacc, hYT⟩ := mem_sdiff.mp hY'
      have hnm := hP2 (c x) hxT Y hYacc hYT hYU
      have : ¬ Movable G S c x Y := fun hmov => hnm ⟨x, mem_cls.mpr ⟨hx, rfl⟩, hmov⟩
      simp only [Movable, not_forall, not_not] at this
      obtain ⟨w, hw, hadj⟩ := this
      rw [mem_cls] at hw
      refine mem_image.mpr ⟨w, mem_nbr.mpr ⟨mem_filter.mpr ⟨hw.1, hw.2 ▸ hYacc⟩, hadj⟩, hw.2⟩
    have h1 := le_trans (card_le_card hQ) card_image_le
    have hUmem : U ∈ acc G S P c lo \ T G S P c lo U :=
      mem_sdiff.mpr ⟨hU, fun hUT => (mem_erase.mp (T_subset U hUT)).1 rfl⟩
    have h2 : Q.card + 1 = _ := card_erase_add_one hUmem
    have h3 : (acc G S P c lo \ T G S P c lo U).card + (T G S P c lo U).card =
        (acc G S P c lo).card := by
      rw [card_sdiff_add_card_eq_card]
      exact fun W hW => (mem_erase.mp (T_subset U hW)).2
    omega
end HajnalSzemeredi.Ctx
