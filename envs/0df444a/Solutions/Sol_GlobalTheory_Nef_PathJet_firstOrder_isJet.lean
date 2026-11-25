-- Prove2me | solution 1 for GlobalTheory.Nef.PathJet.firstOrder_isJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:19:33.889294+00:00
-- url     : https://prove2.me/submissions/37e72f21-125a-4000-9a6c-44df6d251d89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDoublingJetOfOrderTwoFirstOrder
import Theorems.Thm_GlobalTheory_Nef_PathJet_deriv_comp_m
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PathJet
open PowerSeries
namespace GlobalTheory.Nef.PathJet
theorem _root_.solution : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → GlobalTheory.Nef.PathJet.IsJet π ε m β δ 2 (fun f => PowerSeries.C (β (ε f)) + PowerSeries.C (δ f) * PowerSeries.X) := by
  intro A B R _ _ _ π ε m β δ hεπ hmπ hεm hm2 hδ hδπ
  have hεπ' : ∀ b, ε (π b) = b := fun b => by rw [← RingHom.comp_apply, hεπ, RingHom.id_apply]
  have hεm' : ∀ f, ε (m f) = ε f := fun f => by rw [← RingHom.comp_apply, hεm]
  have hδ1 : δ 1 = 0 := by
    have h := hδ 1 1
    simp only [mul_one, map_one, one_mul] at h
    have : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have hdm : ∀ f, δ (m f) = 2 * δ f :=
    deriv_comp_m π ε m β δ hεπ hmπ hm2 hδ hδπ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro f g
    refine ⟨C (-(δ f * δ g)), ?_⟩
    beta_reduce
    rw [hδ, map_mul, map_mul]
    simp only [map_add, map_mul, map_neg]
    ring
  · intro f g
    simp [map_add]
    exact ⟨0, by ring⟩
  · simp [hδ1]
  · intro b
    simp [hεπ', hδπ]
  · intro f
    refine ⟨0, ?_⟩
    beta_reduce
    rw [hεm', hdm]
    have hrC : ∀ x : R, rescale (2 : R) (C x) = C x := by
      intro x; ext n; rw [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]
    simp only [map_add, map_mul, rescale_X, hrC]
    ring
  · intro f
    simp
  · intro f
    simp [coeff_C, coeff_C_mul, coeff_X]
end GlobalTheory.Nef.PathJet
