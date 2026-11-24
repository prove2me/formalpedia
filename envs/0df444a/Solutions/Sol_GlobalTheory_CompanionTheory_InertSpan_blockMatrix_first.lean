-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.blockMatrix_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:54:04.831682+00:00
-- url     : https://prove2.me/submissions/1320a9c5-b0d4-4259-86cc-e20fc79e048f

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
theorem _root_.solution (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    mat3 p M l 0 = p := rfl
end GlobalTheory.CompanionTheory.InertSpan
