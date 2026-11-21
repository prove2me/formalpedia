-- Prove2me | solution 1 for JardenShami.treeOfColoring_downwardClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:56.080187+00:00
-- url     : https://prove2.me/submissions/f1b4180c-8cae-4aa2-8b4b-bd6a1a5cd333

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_mem_fiberRestr
attribute [local simp] JardenShami.Kappa.coe_mk

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type v}
namespace JardenShami
theorem _root_.solution (C : Coloring (Kappa κ) D) :
    ∀ g ∈ treeOfColoring C, ∀ γ : Kappa κ, {p ∈ g | p.1 < γ} ∈ treeOfColoring C := by
  rintro g ⟨δ, β, hβ, rfl⟩ γ
  refine ⟨δ, min β γ, (min_le_left β γ).trans hβ, ?_⟩
  ext ⟨α, d⟩
  simp only [Set.mem_ofPred_eq, mem_fiberRestr, lt_min_iff]
  constructor
  · rintro ⟨⟨h, rfl⟩, hγ⟩
    exact ⟨⟨h, hγ⟩, rfl⟩
  · rintro ⟨⟨h, hγ⟩, rfl⟩
    exact ⟨⟨h, rfl⟩, hγ⟩
end JardenShami
