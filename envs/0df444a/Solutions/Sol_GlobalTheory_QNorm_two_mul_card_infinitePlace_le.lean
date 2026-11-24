-- Prove2me | solution 1 for GlobalTheory.QNorm.two_mul_card_infinitePlace_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:22.589119+00:00
-- url     : https://prove2.me/submissions/dfc6df8e-f538-4620-92a3-197b8cee41c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CardRingHomRealEqNrRealPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionIsGaloisAndEmbeddingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardInfinitePlaceLeQuadratic
import Theorems.Thm_GlobalTheory_QNorm_card_real_eq_pos_add_tReal
import Theorems.Thm_GlobalTheory_QNorm_two_mul_card_pos_le
import Theorems.Thm_GlobalTheory_T_isQuadraticSqrtExtension_basic_facts
import Theorems.Thm_P2M_GlobalTheory_T_card_ringHom_real_eq_nrRealPlaces__cec122734711


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
theorem _root_.solution :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F)
      (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ →
      2 * Fintype.card (InfinitePlace F) ≤ Fintype.card (InfinitePlace E) + tReal F δ := by
  intro F E _ _ _ _ _ δ θ σ h
  have hδ : δ ≠ 0 := fun h0 => h.nonsq (h0 ▸ IsSquare.zero)
  have h1 := card_real_eq_pos_add_tReal F δ hδ
  have h2 := two_mul_card_pos_le F E δ θ σ h
  rw [GlobalTheory.T.card_ringHom_real_eq_nrRealPlaces'] at h1 h2
  have h3 := InfinitePlace.card_add_two_mul_card_eq_rank F
  have h4 := InfinitePlace.card_add_two_mul_card_eq_rank E
  have h5 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
  have h6 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h7 : Module.finrank F E = 2 := (GlobalTheory.T.isQuadraticSqrtExtension_basic_facts F E δ θ σ h).2.2.2.2.2.2
  have h8 := Module.finrank_mul_finrank ℚ F E
  rw [h7] at h8
  omega
end GlobalTheory.QNorm
