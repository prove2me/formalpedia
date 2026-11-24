-- Prove2me | solution 1 for GlobalTheory.T.two_mul_card_infinitePlace_le_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:02.7736+00:00
-- url     : https://prove2.me/submissions/9e54592e-c571-47cb-bec3-48dd8eb31705

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardInfinitePlaceLeQuadratic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulCardInfinitePlaceLeQuadraticStatement
import Theorems.Thm_GlobalTheory_QNorm_two_mul_card_infinitePlace_le


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → 2 * Fintype.card (InfinitePlace F) ≤ Fintype.card (InfinitePlace E) + tReal F δ := by
  first | exact @GlobalTheory.QNorm.two_mul_card_infinitePlace_le | exact GlobalTheory.QNorm.two_mul_card_infinitePlace_le | (intros; apply GlobalTheory.QNorm.two_mul_card_infinitePlace_le <;> assumption)
end _root_.GlobalTheory.T
