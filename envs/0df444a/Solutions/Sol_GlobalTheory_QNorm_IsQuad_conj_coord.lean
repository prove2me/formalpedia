-- Prove2me | solution 1 for GlobalTheory.QNorm.IsQuad.conj_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:42:35.440475+00:00
-- url     : https://prove2.me/submissions/66975b95-6f28-47fb-97fe-e01097f59649

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
namespace GlobalTheory.QNorm
namespace IsQuad
theorem _root_.solution (h : IsQuad δ θ σ) (a b : F) :
    σ (algebraMap F E a + algebraMap F E b * θ) = algebraMap F E a - algebraMap F E b * θ := by
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h.conj]; ring
end IsQuad
end GlobalTheory.QNorm
