-- Prove2me | solution 1 for GlobalTheory.CardGLQuot.natCard_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:23:13.075798+00:00
-- url     : https://prove2.me/submissions/7cfc2335-8c94-4b7f-9ba4-21617f3aa62f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.CardGLQuot
namespace GlobalTheory.CardGLQuot
theorem _root_.solution {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) :
    Nat.card (𝓞 E ⧸ I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
end GlobalTheory.CardGLQuot
