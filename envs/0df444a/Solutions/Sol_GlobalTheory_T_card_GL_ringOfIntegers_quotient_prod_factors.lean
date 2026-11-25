-- Prove2me | solution 1 for GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:13:41.369577+00:00
-- url     : https://prove2.me/submissions/d8ad58e8-4412-4265-bd57-a9e3980edb95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactorsStatement
import Theorems.Thm_GlobalTheory_CardGLQuot_card_GL_quot_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → ∀ n : ℕ,
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n := by
  first | exact @GlobalTheory.CardGLQuot.card_GL_quot_prod | exact GlobalTheory.CardGLQuot.card_GL_quot_prod | (intros; apply GlobalTheory.CardGLQuot.card_GL_quot_prod <;> assumption)
end _root_.GlobalTheory.T
