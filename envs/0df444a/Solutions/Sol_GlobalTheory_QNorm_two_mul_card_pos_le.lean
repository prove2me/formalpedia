-- Prove2me | solution 1 for GlobalTheory.QNorm.two_mul_card_pos_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:29:59.686857+00:00
-- url     : https://prove2.me/submissions/ce9b3bc6-c074-4c9d-a593-15ac10ef5d8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardRingHomRealEqNrRealPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionIsGaloisAndEmbeddingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardInfinitePlaceLeQuadratic
import Theorems.Thm_GlobalTheory_T_isQuadraticSqrtExtension_isGalois_and_embedding


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E) (h : IsQuad δ θ σ) :
    2 * Nat.card {φ : F →+* ℝ // 0 < φ δ} ≤ Nat.card (E →+* ℝ) := by
  classical
  have hext := (GlobalTheory.T.isQuadraticSqrtExtension_isGalois_and_embedding F E δ θ σ h).2.2 ℝ
  have key : ∀ p : Bool × {φ : F →+* ℝ // 0 < φ δ}, ∃ ψ : E →+* ℝ,
      (∀ a : F, ψ (algebraMap F E a) = p.2.1 a) ∧ (0 < ψ θ ↔ p.1 = true) := by
    rintro ⟨b, φ, hφ⟩
    have hs : 0 < Real.sqrt (φ δ) := Real.sqrt_pos.mpr hφ
    cases b
    · obtain ⟨ψ, h1, h2⟩ := hext φ (-Real.sqrt (φ δ)) (by rw [neg_sq, Real.sq_sqrt hφ.le])
      refine ⟨ψ, h1, ?_⟩
      rw [h2]
      simp only [Bool.false_eq_true, iff_false, not_lt]
      linarith
    · obtain ⟨ψ, h1, h2⟩ := hext φ (Real.sqrt (φ δ)) (by rw [Real.sq_sqrt hφ.le])
      refine ⟨ψ, h1, ?_⟩
      rw [h2]
      simpa using hφ
  choose f hf1 hf2 using key
  have hinj : Function.Injective f := by
    intro p q hpq
    refine Prod.ext ?_ (Subtype.ext (RingHom.ext fun a => ?_))
    · have := (hf2 p).symm.trans (hpq ▸ hf2 q)
      exact Bool.eq_iff_iff.mpr this
    · rw [← hf1 p a, ← hf1 q a, hpq]
  have := Nat.card_le_card_of_injective f hinj
  simpa [Nat.card_prod] using this
end GlobalTheory.QNorm
