-- Prove2me | solution 1 for GlobalTheory.NzdDescent.model_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:28:44.986928+00:00
-- url     : https://prove2.me/submissions/0f7a189b-ea6f-476e-a69d-e0a3c388f798

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreGoingDownTensorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonZeroDivisorLocalizationGeneralOfNoetherian
import Theorems.Thm_GlobalTheory_SmoothDescent_cancel_one_tmul
import Theorems.Thm_GlobalTheory_SmoothDescent_exists_fg_subset_range_incl
import Theorems.Thm_GlobalTheory_SmoothDescent_incl_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NzdDescent
open TensorProduct GlobalTheory.SmoothDescent
namespace GlobalTheory.NzdDescent
theorem _root_.solution (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] (b g : B) :
    ∃ (S B₁ : Type) (_ : CommRing S) (_ : IsNoetherianRing S) (_ : Algebra S A) (_ : CommRing B₁)
      (_ : Algebra S B₁) (_ : Algebra.Smooth S B₁) (e : A ⊗[S] B₁ ≃ₐ[A] B) (b₁ g₁ : B₁),
      Function.Injective (fun x : B₁ => e (1 ⊗ₜ x)) ∧ e (1 ⊗ₜ b₁) = b ∧ e (1 ⊗ₜ g₁) = g := by
  classical
  obtain ⟨A₀, B₀, _, _, h₀, hB, ⟨β⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  haveI : IsNoetherianRing A₀ := isNoetherianRing_of_fg h₀
  obtain ⟨S, hS, hsub⟩ := exists_fg_subset_range_incl (C₁ := B₀) ({β b, β g} : Finset _)
  obtain ⟨b₁, hb₁⟩ := hsub (by simp : β b ∈ _)
  obtain ⟨g₁, hg₁⟩ := hsub (by simp : β g ∈ _)
  refine ⟨S, S ⊗[A₀] B₀, inferInstance, isNoetherianRing_of_fg hS, inferInstance, inferInstance,
    inferInstance, inferInstance,
    (Algebra.TensorProduct.cancelBaseChange A₀ S A A B₀).trans β.symm, b₁, g₁, ?_, ?_, ?_⟩
  · intro x y h
    simp only [AlgEquiv.trans_apply, cancel_one_tmul] at h
    exact incl_injective S (β.symm.injective h)
  · simp only [AlgEquiv.trans_apply, cancel_one_tmul]
    exact (congrArg β.symm hb₁).trans (β.symm_apply_apply b)
  · simp only [AlgEquiv.trans_apply, cancel_one_tmul]
    exact (congrArg β.symm hg₁).trans (β.symm_apply_apply g)
end GlobalTheory.NzdDescent
