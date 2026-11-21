-- Prove2me | solution 1 for JardenShami.fiberRestr_eq_iff_histFun_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:04.706374+00:00
-- url     : https://prove2.me/submissions/172037ef-d327-4663-a7b6-dcc9af7054f2

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_fiberRestr_subset_iff_histFun_subset

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution (hT : IsKappaTree κ T) (e : Enumeration κ T)
    {C : Coloring (Kappa κ) (Kappa (levelSup κ T))} (hC : IsTreeColoring e C)
    {β₁ δ₁ β₂ δ₂ : Kappa κ} (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ = fiberRestr C δ₂ β₂ h₂ ↔
      histFun (e.node C β₁ δ₁ h₁) = histFun (e.node C β₂ δ₂ h₂) := by
  rw [subset_antisymm_iff, subset_antisymm_iff,
    fiberRestr_subset_iff_histFun_subset hT e hC, fiberRestr_subset_iff_histFun_subset hT e hC]
end JardenShami
