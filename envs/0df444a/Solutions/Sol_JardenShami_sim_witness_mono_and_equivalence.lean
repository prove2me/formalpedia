-- Prove2me | solution 1 for JardenShami.sim_witness_mono_and_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:52.101126+00:00
-- url     : https://prove2.me/submissions/145efcbf-0687-42c3-9443-23fbc59a0669

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_isStarLocallyAdditive_iff
import Theorems.Thm_JardenShami_Kappa_exists_gt

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C) :
    (∀ (β γ α₁ α₂ : Kappa κ) (hβ : β < α₁) (hγ : γ < α₁) (h₁₂ : α₁ < α₂), β ≠ γ →
        C.color β α₁ hβ = C.color γ α₁ hγ →
          C.color β α₂ (hβ.trans h₁₂) = C.color γ α₂ (hγ.trans h₁₂)) ∧
      Equivalence (Sim C) := by
  have hS := (isStarLocallyAdditive_iff C).1 hC
  have mono : ∀ (β γ α₁ α₂ : Kappa κ) (hβ : β < α₁) (hγ : γ < α₁) (h₁₂ : α₁ < α₂), β ≠ γ →
      C.color β α₁ hβ = C.color γ α₁ hγ →
        C.color β α₂ (hβ.trans h₁₂) = C.color γ α₂ (hγ.trans h₁₂) := by
    intro β γ α₁ α₂ hβ hγ h₁₂ hne h
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (hS β γ α₁ α₂ hlt hγ h₁₂ h.symm).symm
    · exact hS γ β α₁ α₂ hlt hβ h₁₂ h
  refine ⟨mono, ⟨fun β => ?_, fun {β γ} ⟨α, hβ, hγ, h⟩ => ⟨α, hγ, hβ, h.symm⟩, ?_⟩⟩
  · obtain ⟨α, hα⟩ := Kappa.exists_gt hκ.aleph0_le β
    exact ⟨α, hα, hα, rfl⟩
  · rintro β γ δ ⟨α, hβ, hγ, h⟩ ⟨α', hγ', hδ, h'⟩
    obtain ⟨α'', hα''⟩ := Kappa.exists_gt hκ.aleph0_le (max α α')
    have h1 : α < α'' := (le_max_left _ _).trans_lt hα''
    have h2 : α' < α'' := (le_max_right _ _).trans_lt hα''
    -- `α''` witnesses both `β ∼ γ` and `γ ∼ δ`
    have e1 : C.color β α'' (hβ.trans h1) = C.color γ α'' (hγ.trans h1) := by
      by_cases hne : β = γ
      · subst hne; rfl
      · exact mono β γ α α'' hβ hγ h1 hne h
    have e2 : C.color γ α'' (hγ'.trans h2) = C.color δ α'' (hδ.trans h2) := by
      by_cases hne : γ = δ
      · subst hne; rfl
      · exact mono γ δ α' α'' hγ' hδ h2 hne h'
    exact ⟨α'', hβ.trans h1, hδ.trans h2, e1.trans e2⟩
end JardenShami
