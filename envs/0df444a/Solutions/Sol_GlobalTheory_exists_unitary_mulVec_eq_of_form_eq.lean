-- Prove2me | solution 1 for GlobalTheory.exists_unitary_mulVec_eq_of_form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:19.260183+00:00
-- url     : https://prove2.me/submissions/abb27804-2ccf-462d-8f8c-dae9f21bb493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryMulVecEqOfFormEq
import Theorems.Thm_GlobalTheory_exists_quasiReflection_mulVec_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [CharZero E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
      Jᴴ = J → J.det ≠ 0 → ∀ x y : Fin n → E,
      star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y) → star x ⬝ᵥ (J *ᵥ x) ≠ 0 →
      ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  intro E _ _ _ n J hJ _ x y hxy hx
  by_cases h0 : star (x - y) ⬝ᵥ (J *ᵥ x) = 0
  · have hneg : star (-y) ⬝ᵥ (J *ᵥ (-y)) = star y ⬝ᵥ (J *ᵥ y) := by
      rw [star_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    have hyx : star y ⬝ᵥ (J *ᵥ x) = star x ⬝ᵥ (J *ᵥ x) := by
      rw [star_sub, sub_dotProduct, sub_eq_zero] at h0
      exact h0.symm
    have h1 : star (x - -y) ⬝ᵥ (J *ᵥ x) ≠ 0 := by
      rw [sub_neg_eq_add, star_add, add_dotProduct, hyx, ← two_mul]
      exact mul_ne_zero two_ne_zero hx
    obtain ⟨γ, hγ, hγx⟩ := exists_quasiReflection_mulVec_eq J hJ x (-y) (hxy.trans hneg.symm) h1
    refine ⟨-γ, ?_, ?_⟩
    · rw [conjTranspose_neg, neg_mul, mul_neg, neg_mul, neg_neg, hγ]
    · rw [neg_mulVec, hγx, neg_neg]
  · exact exists_quasiReflection_mulVec_eq J hJ x y hxy h0
end GlobalTheory
