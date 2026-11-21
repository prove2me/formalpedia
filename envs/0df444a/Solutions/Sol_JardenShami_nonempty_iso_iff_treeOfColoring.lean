-- Prove2me | solution 1 for JardenShami.nonempty_iso_iff_treeOfColoring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:49:17.860497+00:00
-- url     : https://prove2.me/submissions/0a730d2f-0776-4a9c-a140-24eece13e466

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_nonempty_iso_iff_historyTree
import Theorems.Thm_JardenShami_nonempty_iso_treeOfColoring_historyTree

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution {κ : Cardinal.{w}}
    {T₁ T₂ : Type w} [PartialOrder T₁] [IsTree T₁] [PartialOrder T₂] [IsTree T₂]
    (h₁ : IsKappaTree κ T₁) (h₂ : IsKappaTree κ T₂)
    (hl₁ : ∀ t : T₁, ¬ IsLeaf t) (hl₂ : ∀ t : T₂, ¬ IsLeaf t)
    (e₁ : Enumeration κ T₁) (e₂ : Enumeration κ T₂) (c₁ : e₁.Covers) (c₂ : e₂.Covers)
    {C₁ : Coloring (Kappa κ) (Kappa (levelSup κ T₁))} (hC₁ : IsTreeColoring e₁ C₁)
    {C₂ : Coloring (Kappa κ) (Kappa (levelSup κ T₂))} (hC₂ : IsTreeColoring e₂ C₂) :
    Nonempty (T₁ ≃o T₂) ↔ Nonempty (treeOfColoring C₁ ≃o treeOfColoring C₂) := by
  obtain ⟨i₁⟩ := nonempty_iso_treeOfColoring_historyTree h₁ e₁ c₁ hC₁
  obtain ⟨i₂⟩ := nonempty_iso_treeOfColoring_historyTree h₂ e₂ c₂ hC₂
  rw [nonempty_iso_iff_historyTree hl₁ hl₂]
  constructor
  · rintro ⟨f⟩
    exact ⟨(i₁.trans f).trans i₂.symm⟩
  · rintro ⟨f⟩
    exact ⟨(i₁.symm.trans f).trans i₂⟩
end JardenShami
