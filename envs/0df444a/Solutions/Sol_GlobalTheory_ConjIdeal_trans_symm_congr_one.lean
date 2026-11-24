-- Prove2me | solution 1 for GlobalTheory.ConjIdeal.trans_symm_congr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:42:42.490826+00:00
-- url     : https://prove2.me/submissions/70fc091c-4f22-43eb-ac65-b0fe6381e0a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar
import Theorems.Thm_GlobalTheory_ConjIdeal_dvd_of_addChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ConjIdeal
variable {O : Type*} [CommRing O]
namespace GlobalTheory.ConjIdeal
theorem _root_.solution (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) {M : ℕ} (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C}
    (hζ : IsPrimitiveRoot ζ M) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ X] (e₁ e₂ : X ≃ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, e₂ (x • y) = e₁ (x • y) + M • z)
    (h₂ : ∀ t : AddChar X C, (∀ v, t v ^ M = 1) → ∀ x ∈ I.map bar, ∀ χ : Y,
      t (bar x • e₁.symm χ) = t (bar x • e₂.symm χ)) (y : X) :
    ∃ z : X, e₁.trans e₂.symm y = y + M • z := by
  obtain ⟨z, hz⟩ := dvd_of_addChar bar hbar I hsup hM hζ
    ((e₁.trans e₂.symm).toLinearMap - LinearMap.id) (fun x hx y => by
      obtain ⟨z, hz⟩ := h₁ x hx y
      refine ⟨-e₂.symm z, ?_⟩
      have h : e₁ (x • y) = e₂ (x • y) - M • z := by rw [hz]; abel
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap.id_apply]
      rw [h, map_sub, map_nsmul, e₂.symm_apply_apply, smul_neg]
      abel) (fun t ht x hx y => by
      have h := h₂ t ht x hx (e₁ y)
      rw [e₁.symm_apply_apply] at h
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap.id_apply]
      rw [smul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← h, ← AddChar.map_add_eq_mul,
        add_neg_cancel, AddChar.map_zero_eq_one]) y
  refine ⟨z, ?_⟩
  rw [← hz]
  simp
end GlobalTheory.ConjIdeal
