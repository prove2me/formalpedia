-- Prove2me | solution 1 for JardenShami.fiberRestr_ssubset_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:07.481174+00:00
-- url     : https://prove2.me/submissions/b5b4bad9-0504-417d-b2bc-89d66100707a

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_fiberRestr_eq_fiberRestr

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type w}
namespace JardenShami
theorem _root_.solution {C : Coloring (Kappa κ) D} {δ₁ β₁ δ₂ β₂ : Kappa κ}
    (h₁ : β₁ ≤ δ₁) (h₂ : β₂ ≤ δ₂) :
    fiberRestr C δ₁ β₁ h₁ ⊂ fiberRestr C δ₂ β₂ h₂ ↔
      β₁ < β₂ ∧ ∀ (α : Kappa κ) (hα₁ : α < β₁) (hα₂ : α < β₂),
        C.color α δ₁ (hα₁.trans_le h₁) = C.color α δ₂ (hα₂.trans_le h₂) := by
  constructor
  · rintro ⟨hs, hns⟩
    obtain ⟨hle, hc⟩ := (fiberRestr_subset_iff h₁ h₂).1 hs
    refine ⟨hle.lt_of_ne fun he => hns ?_, hc⟩
    exact (fiberRestr_eq_fiberRestr h₁ h₂ he hc).symm.le
  · rintro ⟨hlt, hc⟩
    refine ⟨(fiberRestr_subset_iff h₁ h₂).2 ⟨hlt.le, hc⟩, fun hs => ?_⟩
    exact hlt.not_ge ((fiberRestr_subset_iff h₂ h₁).1 hs).1
end JardenShami
