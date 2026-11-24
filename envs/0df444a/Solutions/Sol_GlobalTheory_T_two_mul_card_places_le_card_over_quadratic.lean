-- Prove2me | solution 1 for GlobalTheory.T.two_mul_card_places_le_card_over_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:36:09.684983+00:00
-- url     : https://prove2.me/submissions/c439a09b-4d52-4145-a7be-bce9ba29ddbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardPlacesLeCardOverQuadratic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardPlacesLeCardOverQuadraticStatement
import Theorems.Thm_GlobalTheory_QNorm_two_mul_card_le_card_over


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → 2 * S.card ≤ SE.card + tFin F δ S := by
  first | exact @GlobalTheory.QNorm.two_mul_card_le_card_over | exact GlobalTheory.QNorm.two_mul_card_le_card_over | (intros; apply GlobalTheory.QNorm.two_mul_card_le_card_over <;> assumption)
end _root_.GlobalTheory.T
