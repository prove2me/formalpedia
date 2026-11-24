-- Prove2me | solution 1 for GlobalTheory.T.isQuadraticSqrtExtension_isGalois_and_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:16:05.697049+00:00
-- url     : https://prove2.me/submissions/1f202728-e8e7-424f-92cc-a0ced485a303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionIsGaloisAndEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionIsGaloisAndEmbeddingStatement
import Theorems.Thm_GlobalTheory_QNorm_isQuad_galois_and_embedding


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → IsGalois F E ∧ (∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ) ∧ ∀ (L : Type) [Field L] (φ : F →+* L) (r : L), r ^ 2 = φ δ → ∃ ψ : E →+* L, (∀ a : F, ψ (algebraMap F E a) = φ a) ∧ ψ θ = r := by
  first | exact @GlobalTheory.QNorm.isQuad_galois_and_embedding | exact GlobalTheory.QNorm.isQuad_galois_and_embedding | (intros; apply GlobalTheory.QNorm.isQuad_galois_and_embedding <;> assumption)
end _root_.GlobalTheory.T
