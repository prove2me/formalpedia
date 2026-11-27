-- Prove2me | solution 1 for GlobalTheory.T.hasSum_tuple_prod_of_summable_norm_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T06:12:50.735127+00:00
-- url     : https://prove2.me/submissions/7e1f526c-4ca6-4cc0-9390-b4367dd5693f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumTupleProdOfSummableNormComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SplitHeightSummableExpNegAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumTupleProdOfSummableNormComplexStatement
import Theorems.Thm_GlobalTheory_hasSum_pi_prod_of_summable_norm


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
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (J : ι → Type) (f : ∀ i, J i → ℂ), (∀ i, Summable (fun j => ‖f i j‖)) → HasSum (fun j : ∀ i, J i => ∏ i, f i (j i)) (∏ i, ∑' j, f i j) := by
  first | exact @GlobalTheory.hasSum_pi_prod_of_summable_norm | exact GlobalTheory.hasSum_pi_prod_of_summable_norm | (intros; apply GlobalTheory.hasSum_pi_prod_of_summable_norm <;> assumption)
end _root_.GlobalTheory.T
