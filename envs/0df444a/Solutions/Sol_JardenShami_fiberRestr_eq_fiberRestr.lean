-- Prove2me | solution 1 for JardenShami.fiberRestr_eq_fiberRestr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:45.291217+00:00
-- url     : https://prove2.me/submissions/3c1a2c16-12ac-4f27-a72a-7f318751d427

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type w}
namespace JardenShami
theorem _root_.solution {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ}
    (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) (hβ : β₁ = β₂)
    (hc : ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
      C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂)) :
    fiberRestr C δ₁ β₁ h₁ = fiberRestr C δ₂ β₂ h₂ :=
  ((fiberRestr_subset_iff h₁ h₂).2 ⟨hβ.le, hc⟩).antisymm
    ((fiberRestr_subset_iff h₂ h₁).2 ⟨hβ.ge, fun α hα₂ hα₁ => (hc α hα₁ hα₂).symm⟩)
end JardenShami
