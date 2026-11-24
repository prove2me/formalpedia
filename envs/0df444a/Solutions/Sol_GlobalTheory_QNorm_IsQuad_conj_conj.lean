-- Prove2me | solution 1 for GlobalTheory.QNorm.IsQuad.conj_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:57:25.384901+00:00
-- url     : https://prove2.me/submissions/39466462-1443-4819-9256-854e25d05838

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsQuadraticSqrtExtensionBasicFacts
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_conj_coord

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
theorem _root_.solution (h : IsQuad δ θ σ) (x : E) : σ (σ x) = x := by
  obtain ⟨a, b, rfl⟩ := h.span x
  rw [h.conj_coord, map_sub, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, h.conj]; ring
end IsQuad
end GlobalTheory.QNorm
