-- Prove2me | solution 1 for JardenShami.fiberRestr_colorMinOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:45.644172+00:00
-- url     : https://prove2.me/submissions/e48c2793-48c4-4382-b5ac-b76b94ef2ee5

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_mk
import Theorems.Thm_JardenShami_mem_fiberRestr
import Theorems.Thm_JardenShami_colorMinOf_color
attribute [local simp] JardenShami.Kappa.coe_mk

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type v}
namespace JardenShami
theorem _root_.solution (f : Kappa κ → Fin 2) (δ β : Kappa κ) (hβ : β ≤ δ) :
    fiberRestr (colorMinOf f) δ β hβ = {p | p.1 < β ∧ p.2 = f p.1} := by
  ext ⟨α, d⟩
  simp only [mem_fiberRestr, colorMinOf_color, Set.mem_ofPred_eq]
  exact ⟨fun ⟨h, hd⟩ => ⟨h, hd⟩, fun ⟨h, hd⟩ => ⟨h, hd⟩⟩
end JardenShami
