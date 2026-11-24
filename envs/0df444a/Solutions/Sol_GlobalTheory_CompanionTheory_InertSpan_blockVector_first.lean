-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.blockVector_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:55:11.36099+00:00
-- url     : https://prove2.me/submissions/92a7d37d-e460-4e8b-81dd-69794333ccb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertSpan
variable {L : Type} [Field L] {N : ℕ}
namespace GlobalTheory.CompanionTheory.InertSpan
theorem _root_.solution (x : L) (w : Fin N → L) (t : L) : vec3 x w t 0 = x := rfl
end GlobalTheory.CompanionTheory.InertSpan
