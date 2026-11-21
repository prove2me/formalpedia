-- Prove2me | solution 1 for JardenShami.two_power_le_mk_lim_binTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:55.268436+00:00
-- url     : https://prove2.me/submissions/4b0b814c-21c1-4068-a51a-a58a6235c5b2

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Theorems.Thm_JardenShami_height_binTree
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_eq
import Theorems.Thm_JardenShami_Kappa_mk_coe
import Theorems.Thm_JardenShami_Kappa_mk_eq
import Theorems.Thm_JardenShami_Tree_isCofinalBranch_iff
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe



set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {ν : Cardinal.{w}}
namespace JardenShami
theorem _root_.solution (hν : ℵ₀ ≤ ν) : 2 ^ ν ≤ #(Lim (binTree ν)) := by
  classical
  have hgt : ∀ α : Kappa ν, ∃ β : Kappa ν, α < β := fun α => by
    obtain ⟨β, -, h⟩ := Kappa.exists_gt_of_card_eq hν
      (show #(Set.univ : Set (Kappa ν)) = ν by rw [Cardinal.mk_univ, Kappa.mk_eq]) α
    exact ⟨β, h⟩
  let node : (Kappa ν → Fin 2) → Kappa ν → binTree ν := fun f β => ⟨binRestr f β, f, β, rfl⟩
  have hnode_inj : ∀ f, Function.Injective (node f) := fun f β β' h =>
    (binRestr_eq_iff.1 (congrArg Subtype.val h)).1
  let br : (Kappa ν → Fin 2) → Set (binTree ν) := fun f => Set.range (node f)
  have hchain : ∀ f, IsChain (· ≤ ·) (br f) := by
    rintro f _ ⟨β, rfl⟩ _ ⟨β', rfl⟩ -
    rcases le_total β β' with h | h
    · exact Or.inl (show binRestr f β ⊆ binRestr f β' from
        binRestr_subset_iff.2 ⟨h, fun _ _ => rfl⟩)
    · exact Or.inr (show binRestr f β' ⊆ binRestr f β from
        binRestr_subset_iff.2 ⟨h, fun _ _ => rfl⟩)
  have hbranch : ∀ f, IsBranch (br f) := by
    intro f
    refine ⟨hchain f, fun c hc hsub => hsub.antisymm fun x hx => ?_⟩
    obtain ⟨_, f', β', rfl⟩ := x
    obtain ⟨β'', hβ''⟩ := hgt β'
    have hy : node f β'' ∈ c := hsub ⟨β'', rfl⟩
    have hne : (⟨binRestr f' β', f', β', rfl⟩ : binTree ν) ≠ node f β'' := fun h =>
      hβ''.ne (binRestr_eq_iff.1 (congrArg Subtype.val h)).1
    rcases hc hx hy hne with h | h
    · have hs : binRestr f' β' ⊆ binRestr f β'' := h
      obtain ⟨-, hag⟩ := binRestr_subset_iff.1 hs
      exact ⟨β', Subtype.ext (binRestr_eq_iff.2 ⟨rfl, fun α hα => (hag α hα).symm⟩)⟩
    · have hs : binRestr f β'' ⊆ binRestr f' β' := h
      exact absurd (binRestr_subset_iff.1 hs).1 (not_le.2 hβ'')
  have hlim : ∀ f, br f ∈ Lim (binTree ν) := by
    intro f
    refine (isCofinalBranch_iff height_binTree).2 ⟨hbranch f, ?_⟩
    rw [Cardinal.mk_range_eq _ (hnode_inj f), Kappa.mk_eq]
  let Φ : (Kappa ν → Fin 2) → Lim (binTree ν) := fun f => ⟨br f, hlim f⟩
  have hΦ : Function.Injective Φ := by
    intro f f' h
    funext α
    obtain ⟨β, hβ⟩ := hgt α
    have hmem : node f β ∈ br f' := by
      have := congrArg Subtype.val h
      change br f = br f' at this
      rw [← this]
      exact ⟨β, rfl⟩
    obtain ⟨β', hβ'⟩ := hmem
    have := (binRestr_eq_iff.1 (congrArg Subtype.val hβ')).2
    exact (this α (hβ.trans_le (binRestr_eq_iff.1 (congrArg Subtype.val hβ')).1.ge)).symm
  calc 2 ^ ν = #(Kappa ν → Fin 2) := by simp
    _ ≤ #(Lim (binTree ν)) := Cardinal.mk_le_of_injective hΦ
end JardenShami
