-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.exists_TU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:49:18.535975+00:00
-- url     : https://prove2.me/submissions/29dc9346-5e89-48b0-aade-ea03a649464f

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_split_avoid
public import Theorems.Thm_HajnalSzemeredi_rtgMono
public import Theorems.Thm_HajnalSzemeredi_Ctx_lo_mem_acc
public import Theorems.Thm_HajnalSzemeredi_Ctx_T_lo_nonempty
public import Theorems.Thm_HajnalSzemeredi_exists_step_avoid


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
    ∃ U ∈ acc G S P c lo, (T G S P c lo U).Nonempty ∧
      (∀ W ∈ T G S P c lo U, ∀ X ∈ (acc G S P c lo).erase W,
        ReflTransGen (avoid G S c W) X lo) ∧
      (∀ X ∈ T G S P c lo U, ∀ Y ∈ acc G S P c lo, Y ∉ T G S P c lo U → Y ≠ U →
        ¬ Mov G S c X Y) := by
  set NT := (acc G S P c lo).filter fun W => (T G S P c lo W).Nonempty
  have hNT : NT.Nonempty := ⟨lo, mem_filter.mpr ⟨h.lo_mem_acc, h.T_lo_nonempty⟩⟩
  obtain ⟨U, hU, hmin⟩ := exists_min_image NT (fun W => (T G S P c lo W).card) hNT
  obtain ⟨hUacc, hUne⟩ := mem_filter.mp hU
  refine ⟨U, hUacc, hUne, ?_, ?_⟩
  · -- toda clase de `T_U` es terminal
    intro W hW X hX
    obtain ⟨hWU', hWnot⟩ := mem_filter.mp hW
    obtain ⟨hWU, hWacc⟩ := mem_erase.mp hWU'
    have hsub : T G S P c lo W ⊆ (T G S P c lo U).erase W := by
      intro Y hY
      obtain ⟨hYW', hYnot⟩ := mem_filter.mp hY
      obtain ⟨hYW, hYacc⟩ := mem_erase.mp hYW'
      refine mem_erase.mpr ⟨hYW, ?_⟩
      have hYU : Y ≠ U := by
        rintro rfl
        have hUlo : Y ≠ lo := by rintro rfl; exact hYnot ReflTransGen.refl
        obtain ⟨j, hj, hjU, hjpath⟩ := exists_step_avoid (mem_filter.mp hYacc).2 hUlo
        have hjW : j ≠ W := by rintro rfl; exact hWnot hjpath
        rcases split_avoid (x := W) hjpath hjW with hp | hp
        · exact hYnot (ReflTransGen.head ⟨hj, hWU.symm, hjW⟩
            (rtgMono hp (fun a b hab => ⟨hab.1.1, hab.2.1, hab.2.2⟩)))
        · exact hWnot hp
      refine mem_filter.mpr ⟨mem_erase.mpr ⟨hYU, hYacc⟩, fun hp => ?_⟩
      rcases split_avoid (x := W) hp hYW with hp' | hp'
      · exact hYnot (rtgMono hp' (fun a b hab => ⟨hab.1.1, hab.2.1, hab.2.2⟩))
      · exact hWnot hp'
    have hTW : T G S P c lo W = ∅ := by
      by_contra hne
      have hWNT : W ∈ NT := mem_filter.mpr ⟨hWacc, nonempty_iff_ne_empty.mpr hne⟩
      exact absurd (hmin W hWNT)
        (not_le.mpr (lt_of_le_of_lt (card_le_card hsub) (card_erase_lt_of_mem hW)))
    by_contra hnot
    have : X ∈ T G S P c lo W := mem_filter.mpr ⟨hX, hnot⟩
    rw [hTW] at this
    exact notMem_empty _ this
  · -- ninguna clase de `T_U` es movible a una clase de `(𝒜 \ 𝒜') \ {U}`
    intro X hX Y hY hYT hYU hmov
    obtain ⟨hXU', hXnot⟩ := mem_filter.mp hX
    have hXU := (mem_erase.mp hXU').1
    have hYreach : ReflTransGen (avoid G S c U) Y lo := by
      by_contra hn
      exact hYT (mem_filter.mpr ⟨mem_erase.mpr ⟨hYU, hY⟩, hn⟩)
    exact hXnot (ReflTransGen.head ⟨hmov, hXU, hYU⟩ hYreach)
end HajnalSzemeredi.Ctx
