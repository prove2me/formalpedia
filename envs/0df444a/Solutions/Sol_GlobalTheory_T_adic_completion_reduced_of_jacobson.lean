-- Prove2me | solution 1 for GlobalTheory.T.adic_completion_reduced_of_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:58:01.665856+00:00
-- url     : https://prove2.me/submissions/51dc2fa1-b457-440a-b4b5-f326a9359ec6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionReducedOfJacobson
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionReducedOfJacobsonStatement
import Theorems.Thm_GlobalTheory_CompletionReduced_isReduced_adicCompletion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D] (J : Ideal D), J ≤ Ideal.jacobson (⊥ : Ideal D) → IsReduced (AdicCompletion J D) := by
  first | exact @GlobalTheory.CompletionReduced.isReduced_adicCompletion | exact GlobalTheory.CompletionReduced.isReduced_adicCompletion | (intros; apply GlobalTheory.CompletionReduced.isReduced_adicCompletion <;> assumption)
end _root_.GlobalTheory.T
