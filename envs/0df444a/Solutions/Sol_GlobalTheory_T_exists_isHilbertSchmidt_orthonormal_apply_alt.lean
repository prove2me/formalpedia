-- Prove2me | solution 1 for GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:08:56.832883+00:00
-- url     : https://prove2.me/submissions/c7c8223f-ece5-431b-be0b-30e961aff7e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsHilbertSchmidtOrthonormalApply
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SplitHeightSummableExpNegAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsHilbertSchmidtOrthonormalApplyStatement
import Theorems.Thm_GlobalTheory_exists_isHilbertSchmidt_orthonormal_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : Type) (u : J → H) (w : J → K), Orthonormal ℂ u → Summable (fun j => ‖w j‖ ^ 2) → ∃ G : H →L[ℂ] K, (∀ j, G (u j) = w j) ∧ (∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0) ∧ GlobalTheory.OpTrace.IsHilbertSchmidt G := by
  first | exact @GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply | exact GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply | (intros; apply GlobalTheory.exists_isHilbertSchmidt_orthonormal_apply <;> assumption)
end _root_.GlobalTheory.T
