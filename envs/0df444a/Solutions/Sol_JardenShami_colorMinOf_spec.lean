-- Prove2me | solution 1 for JardenShami.colorMinOf_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:56.602192+00:00
-- url     : https://prove2.me/submissions/2af5f757-6eef-4f2f-83c4-31481c5b678d

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_colorMinOf_color
import Theorems.Thm_JardenShami_colorMinOf_color_dual
import Theorems.Thm_JardenShami_fiberRestr_colorMinOf
attribute [local simp] JardenShami.Kappa.coe_mk

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type v}
namespace JardenShami
theorem _root_.solution (f : Kappa κ → Fin 2) :
    IsLocallyAdditive (colorMinOf f) ∧ IsStarLocallyAdditive (colorMinOf f) ∧
      Nonempty (treeOfColoring (colorMinOf f) ≃o Kappa κ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d hab hbc hcd _
    rw [colorMinOf_color, colorMinOf_color]
  · intro a b c d hab hbc hcd h
    rw [colorMinOf_color_dual, colorMinOf_color_dual] at h ⊢
    exact h
  · let φ : Kappa κ → treeOfColoring (colorMinOf f) :=
      fun β => ⟨fiberRestr (colorMinOf f) β β le_rfl, β, β, le_rfl, rfl⟩
    have hφ : ∀ a b, φ a ≤ φ b ↔ a ≤ b := by
      intro a b
      change fiberRestr _ a a le_rfl ⊆ fiberRestr _ b b le_rfl ↔ a ≤ b
      rw [fiberRestr_subset_iff]
      refine ⟨fun h => h.1, fun h => ⟨h, fun α _ _ => ?_⟩⟩
      rw [colorMinOf_color, colorMinOf_color]
    refine ⟨(RelIso.ofSurjective (OrderEmbedding.ofMapLEIff φ hφ) ?_).symm⟩
    rintro ⟨_, δ, β, hβ, rfl⟩
    refine ⟨β, Subtype.ext ?_⟩
    change fiberRestr _ β β le_rfl = fiberRestr _ δ β hβ
    rw [fiberRestr_colorMinOf, fiberRestr_colorMinOf]
end JardenShami
