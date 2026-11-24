-- Prove2me | solution 1 for GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:11.864085+00:00
-- url     : https://prove2.me/submissions/5cae6157-623a-48eb-a4c9-66ec1504baf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquare
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsQuadraticSqrtExtensionOfNotSquareStatement
import Theorems.Thm_GlobalTheory_QNorm_exists_isQuad


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ := by
  first | exact @GlobalTheory.QNorm.exists_isQuad | exact GlobalTheory.QNorm.exists_isQuad | (intros; apply GlobalTheory.QNorm.exists_isQuad <;> assumption)
end _root_.GlobalTheory.T
