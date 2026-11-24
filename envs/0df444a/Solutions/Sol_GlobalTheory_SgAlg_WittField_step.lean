-- Prove2me | solution 1 for GlobalTheory.SgAlg.WittField.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:45.179021+00:00
-- url     : https://prove2.me/submissions/8d8917ec-270f-4cb2-b1ae-7e16a60458ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionHermitianFrames
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_sub_left
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_smul_left
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_sub_right
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_smul_right
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_conj
import Theorems.Thm_GlobalTheory_SgAlg_WittField_form_add_right
import Theorems.Thm_GlobalTheory_SgAlg_WittField_isUn_mul
import Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_mulVec
import Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_form
import Theorems.Thm_GlobalTheory_SgAlg_WittField_isUn_qr
import Theorems.Thm_GlobalTheory_SgAlg_WittField_qr_fix
import Theorems.Thm_GlobalTheory_SgAlg_WittField_stepA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittField
variable {E : Type} [Field E] {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.SgAlg.WittField
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (hJ : cT σ J = J) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    (h2 : (2 : E) ≠ 0) {a : ℕ} (y : Fin a → Fin n → E)
    (x x' : Fin n → E) (hy : ∀ i, form σ J (y i) x = form σ J (y i) x')
    (hxx : form σ J x x = form σ J x' x') (u₁ u₂ : Fin n → E)
    (hu₁ : ∀ i, form σ J (y i) u₁ = 0) (hxu₁ : form σ J x u₁ = 1)
    (hu₂ : ∀ i, form σ J (y i) u₂ = 0) (hxu₂ : form σ J x' u₂ = 1) :
    ∃ g, IsUn σ J g ∧ (∀ i, g *ᵥ y i = y i) ∧ g *ᵥ x = x' := by
  by_cases hc : form σ J x (x - x') ≠ 0
  · exact stepA hσ hJ y x x' hy hxx hc
  push_neg at hc

  obtain ⟨u, hu, hxu, hx'u⟩ : ∃ u : Fin n → E, (∀ i, form σ J (y i) u = 0) ∧
      form σ J x u ≠ 0 ∧ form σ J x' u ≠ 0 := by
    by_cases h1 : form σ J x' u₁ ≠ 0
    · exact ⟨u₁, hu₁, by rw [hxu₁]; exact one_ne_zero, h1⟩
    by_cases h2' : form σ J x u₂ ≠ 0
    · exact ⟨u₂, hu₂, h2', by rw [hxu₂]; exact one_ne_zero⟩
    push_neg at h1 h2'
    refine ⟨u₁ + u₂, fun i => ?_, ?_, ?_⟩
    · rw [form_add_right, hu₁, hu₂]; simp
    · rw [form_add_right, hxu₁, h2']; simp
    · rw [form_add_right, h1, hxu₂]; simp

  obtain ⟨l, hl0, hl⟩ : ∃ l : E, l ≠ 0 ∧ l * σ l * form σ J u u = l + σ l := by
    by_cases hN : form σ J u u = 0
    · exact ⟨δ, hδ, by rw [hN, hσδ]; ring⟩
    · have hσN : σ (form σ J u u) = form σ J u u := (form_conj hσ hJ u u).symm
      refine ⟨2 / form σ J u u, div_ne_zero h2 hN, ?_⟩
      rw [map_div₀, hσN, map_ofNat]
      field_simp; ring
  set z := qr σ J u l *ᵥ x with hz
  have hzx : z = x - (l * form σ J x u) • u := qr_mulVec u l x
  obtain ⟨g, hg, hgy, hgz⟩ := stepA hσ hJ y z x' (fun i => by
      rw [hzx, form_sub_right, form_smul_right, hu i, mul_zero, sub_zero, hy i])
    (by rw [hz, qr_form hσ hJ u l hl, hxx])
    (by
      have hval : form σ J z (z - x') = l * form σ J x u * form σ J u x' := by
        rw [hzx]
        simp only [form_sub_left, form_sub_right, form_smul_left, form_smul_right, map_mul]
        rw [form_sub_right] at hc
        rw [form_conj hσ hJ x u]
        linear_combination hc + (form σ J x u * σ (form σ J x u)) * hl
      rw [hval, form_conj hσ hJ x' u]
      refine mul_ne_zero (mul_ne_zero hl0 hxu) ?_
      intro h; apply hx'u; rw [← hσ (form σ J x' u), h, map_zero])
  refine ⟨g * qr σ J u l, isUn_mul hg (isUn_qr hσ hJ u l hl), fun i => ?_, ?_⟩
  · rw [← mulVec_mulVec, qr_fix u l (y i) (hu i), hgy i]
  · rw [← mulVec_mulVec, ← hz, hgz]
end GlobalTheory.SgAlg.WittField
