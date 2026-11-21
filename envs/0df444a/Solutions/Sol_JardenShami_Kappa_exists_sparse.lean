-- Prove2me | solution 1 for JardenShami.Kappa.exists_sparse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:57.828762+00:00
-- url     : https://prove2.me/submissions/a85039ea-b28a-4eb7-9c10-807fa4add26c

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Theorems.Thm_JardenShami_Kappa_mk_Iic_lt
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_eq
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_lt
import Theorems.Thm_JardenShami_Kappa_card_eq_of_forall_exists_gt

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}}
namespace JardenShami
namespace Kappa
theorem _root_.solution (hκ : κ.IsRegular) {Γ : Set (Kappa κ)} (hΓ : #Γ = κ)
    (F : Kappa κ → Kappa κ) :
    ∃ Γ' ⊆ Γ, #Γ' = κ ∧ ∀ γ₀ ∈ Γ', ∀ γ ∈ Γ', γ₀ < γ → F γ₀ < γ := by
  obtain ⟨P, hP⟩ : ∃ P : Kappa κ → Prop,
      ∀ γ, P γ ↔ γ ∈ Γ ∧ ∀ γ₀ (_ : γ₀ < γ), P γ₀ → F γ₀ < γ :=
    ⟨wellFounded_lt.fix fun γ ih => γ ∈ Γ ∧ ∀ γ₀ (h : γ₀ < γ), ih γ₀ h → F γ₀ < γ,
      fun γ => by rw [WellFounded.fix_eq]⟩
  refine ⟨{γ | P γ}, fun γ hγ => ((hP γ).1 hγ).1, ?_,
    fun γ₀ h₀ γ hγ hlt => ((hP γ).1 hγ).2 γ₀ hlt h₀⟩
  refine Kappa.card_eq_of_forall_exists_gt hκ fun x => ?_
  by_contra hc
  push Not at hc
  have hsmall : #{γ | P γ} < κ :=
    (Cardinal.mk_le_mk_of_subset fun y hy => hc y hy).trans_lt
      (Kappa.mk_Iic_lt hκ.aleph0_le x)
  obtain ⟨z, hz⟩ := Kappa.exists_gt_of_card_lt hκ
    (Cardinal.mk_image_le.trans_lt hsmall : #(F '' {γ | P γ}) < κ)
  obtain ⟨γ, hγΓ, hγ⟩ := Kappa.exists_gt_of_card_eq hκ.aleph0_le hΓ (max x z)
  have hPγ : P γ := (hP γ).2 ⟨hγΓ, fun γ₀ _ h₀ =>
    (hz _ ⟨γ₀, h₀, rfl⟩).trans ((le_max_right _ _).trans_lt hγ)⟩
  exact (hc γ hPγ).not_gt ((le_max_left _ _).trans_lt hγ)
end Kappa
end JardenShami
