-- Prove2me | solution 1 for JardenShami.colorMaxOf_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:00.054977+00:00
-- url     : https://prove2.me/submissions/cd6037a7-1bd0-4d9f-a9c0-ac70cb2f517b

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_mem_fiberRestr
import Theorems.Thm_JardenShami_colorMaxOf_color
import Theorems.Thm_JardenShami_colorMaxOf_color_dual
attribute [local simp] JardenShami.Kappa.coe_mk

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type v}
namespace JardenShami
theorem _root_.solution (f : Kappa κ → Fin 2)
    (hf : ¬ ∃ (α₀ : Kappa κ) (i : Fin 2), ∀ β, α₀ ≤ β → f β = i) :
    IsLocallyAdditive (colorMaxOf f) ∧ IsStarLocallyAdditive (colorMaxOf f) ∧
      treeOfColoring (colorMaxOf f) =
        {g | ∃ (β : Kappa κ) (i : Fin 2), g = {p | p.1 < β ∧ p.2 = i}} := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d hab hbc hcd h
    rw [colorMaxOf_color, colorMaxOf_color] at h ⊢
    exact h
  · intro a b c d hab hbc hcd _
    rw [colorMaxOf_color_dual, colorMaxOf_color_dual]
  · have hfr : ∀ (δ β : Kappa κ) (hβ : β ≤ δ),
        fiberRestr (colorMaxOf f) δ β hβ = {p | p.1 < β ∧ p.2 = f δ} := by
      intro δ β hβ
      ext ⟨α, d⟩
      simp only [mem_fiberRestr, colorMaxOf_color, Set.mem_ofPred_eq]
      exact ⟨fun ⟨h, hd⟩ => ⟨h, hd⟩, fun ⟨h, hd⟩ => ⟨h, hd⟩⟩
    ext g
    constructor
    · rintro ⟨δ, β, hβ, rfl⟩
      exact ⟨β, f δ, hfr δ β hβ⟩
    · rintro ⟨β, i, rfl⟩
      obtain ⟨δ, hδ, hfδ⟩ : ∃ δ, β ≤ δ ∧ f δ = i := by
        by_contra hc
        push Not at hc
        have key : ∀ i j : Fin 2, j ≠ i → j = i + 1 := by decide
        exact hf ⟨β, i + 1, fun δ hδ => key i _ (hc δ hδ)⟩
      exact ⟨δ, β, hδ, by rw [hfr, hfδ]⟩
end JardenShami
