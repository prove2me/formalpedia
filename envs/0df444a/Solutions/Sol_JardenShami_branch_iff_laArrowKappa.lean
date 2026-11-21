-- Prove2me | solution 1 for JardenShami.branch_iff_laArrowKappa
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:21.843524+00:00
-- url     : https://prove2.me/submissions/dfcdebb9-5bc8-4587-82ff-f25b1f578712

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_eq
import Theorems.Thm_JardenShami_IsLocallyAdditive_comp_injective
import Theorems.Thm_JardenShami_Tree_mk_le_of_isChain
import Theorems.Thm_JardenShami_exists_enumeration
import Theorems.Thm_JardenShami_laArrowKappa_of_forall_branch
import Theorems.Thm_JardenShami_Enumeration_ht_t
import Theorems.Thm_JardenShami_Kappa_coe_inj
import Theorems.Thm_JardenShami_Kappa_coe_lt_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_Kappa_mk_coe
import Theorems.Thm_JardenShami_existsUnique_isTreeColoring
import Theorems.Thm_JardenShami_isLocallyAdditive_of_isTreeColoring
import Theorems.Thm_JardenShami_lt_of_le_of_le_of_ht_lt
attribute [local simp] JardenShami.Kappa.coe_mk
attribute [local simp] JardenShami.Kappa.mk_coe



set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hunc : ℵ₀ < κ)
    (hμ : μ < κ) :
    (∀ (T : Type w) [PartialOrder T] [IsTree T], height T = κ.ord →
        (∀ α : Ordinal.{w}, #(Lev T α) ≤ μ) → ∃ b : Set T, IsBranch b ∧ #b = κ) ↔
      LaArrowKappa κ μ := by
  classical
  have hκ0 : ℵ₀ ≤ κ := hunc.le
  constructor
  · -- (1) ⇒ (2)
    exact laArrowKappa_of_forall_branch κ μ hκ hμ
  · -- (2) ⇒ (1)
    intro h2 T _ _ hT hlev
    have hTk : IsKappaTree κ T := ⟨hT, fun α _ => (hlev α).trans_lt hμ⟩
    obtain ⟨e⟩ := exists_enumeration (Cardinal.aleph0_pos.trans_le hκ0).ne' hTk
    obtain ⟨C, hCe, -⟩ := existsUnique_isTreeColoring hTk e
    have hla := isLocallyAdditive_of_isTreeColoring e hCe
    -- the colors of `C(T,e)` are `< levelSup ≤ μ`
    have hsup : (levelSup κ T).ord ≤ μ.ord :=
      Cardinal.ord_le_ord.2 (ciSup_le' fun α => hlev _)
    let ι : Kappa (levelSup κ T) → Kappa μ := fun x =>
      Kappa.mk (x : Ordinal.{w}) ((Kappa.coe_lt_ord x).trans_le hsup)
    have hι : Function.Injective ι := by
      intro x y h
      have := congrArg (fun z : Kappa μ => (z : Ordinal.{w})) h
      simp only [ι, Kappa.coe_mk] at this
      exact Kappa.coe_inj.1 this
    obtain ⟨H, hH, hHom⟩ := h2 (ι ∘ C) (hla.comp_injective hι)
    have hHomC : IsHomogeneous C H := fun p q hp hq => hι (hHom p q hp hq)
    -- the common color `i`
    obtain ⟨x₀, hx₀⟩ : H.Nonempty := by
      rw [← Set.nonempty_coe_sort, ← Cardinal.mk_ne_zero_iff, hH]
      exact (Cardinal.aleph0_pos.trans_le hκ0).ne'
    obtain ⟨y₀, hy₀, hxy₀⟩ := Kappa.exists_gt_of_card_eq hκ0 hH x₀
    set i := C.color x₀ y₀ hxy₀ with hi
    have hcol : ∀ α ∈ H, ∀ δ ∈ H, ∀ h : α < δ, C.color α δ h = i := by
      intro α hα δ hδ h
      refine hHomC _ _ ?_ ?_
      · intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact hα
        · exact hδ
      · intro z hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact hx₀
        · exact hy₀
    -- `{t^i_α : α ∈ H}` is a chain of size `κ`
    have hilt : ∀ α ∈ H, (i : Ordinal.{w}) < (#(Lev T (α : Ordinal.{w}))).ord := by
      intro α hα
      obtain ⟨δ, hδ, hαδ⟩ := Kappa.exists_gt_of_card_eq hκ0 hH α
      have := (hCe α δ hαδ).1
      rwa [hcol α hα δ hδ hαδ] at this
    have hht : ∀ α ∈ H, ht (e.t α i) = α := fun α hα =>
      e.ht_t (Kappa.coe_lt_ord α) (hilt α hα)
    have hlt : ∀ α ∈ H, ∀ β ∈ H, α < β → e.t α i < e.t β i := by
      intro α hα β hβ hαβ
      obtain ⟨γ, hγ, hβγ⟩ := Kappa.exists_gt_of_card_eq hκ0 hH β
      have h₁ := (hCe α γ (hαβ.trans hβγ)).2
      have h₂ := (hCe β γ hβγ).2
      rw [hcol α hα γ hγ] at h₁
      rw [hcol β hβ γ hγ] at h₂
      refine lt_of_le_of_le_of_ht_lt h₁ h₂ ?_
      rw [hht α hα, hht β hβ]
      exact Kappa.coe_lt_coe.2 hαβ
    let S : Set T := (fun α : Kappa κ => e.t α i) '' H
    have hSchain : IsChain (· ≤ ·) S := by
      rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ hne
      rcases lt_trichotomy α β with h | rfl | h
      · exact Or.inl (hlt α hα β hβ h).le
      · exact absurd rfl hne
      · exact Or.inr (hlt β hβ α hα h).le
    have hinjS : Set.InjOn (fun α : Kappa κ => e.t α i) H := by
      intro α hα β hβ h
      have := congrArg ht h
      simp only [hht α hα, hht β hβ] at this
      exact Kappa.coe_inj.1 this
    have hScard : #S = κ := by rw [Cardinal.mk_image_eq_of_injOn _ _ hinjS, hH]
    -- extend it to a branch
    obtain ⟨M, hM, hSM⟩ := hSchain.exists_maxChain
    refine ⟨M, hM, le_antisymm (mk_le_of_isChain hT hM.1) ?_⟩
    rw [← hScard]
    exact Cardinal.mk_le_mk_of_subset hSM
end JardenShami
