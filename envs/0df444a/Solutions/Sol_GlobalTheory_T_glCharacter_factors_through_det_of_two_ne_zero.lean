-- Prove2me | solution 1 for GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:19:26.13708+00:00
-- url     : https://prove2.me/submissions/cd924886-ec3d-485f-93fd-89f41a9cfd04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZeroStatement
import Theorems.Thm_GlobalTheory_ghom_factors_through_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k], (2 : k) ≠ 0 → ∀ {n : ℕ} (c : GL (Fin n) k →* ℂˣ),
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) := by
  first | exact @GlobalTheory.ghom_factors_through_det | exact GlobalTheory.ghom_factors_through_det | (intros; apply GlobalTheory.ghom_factors_through_det <;> assumption)
end _root_.GlobalTheory.T
