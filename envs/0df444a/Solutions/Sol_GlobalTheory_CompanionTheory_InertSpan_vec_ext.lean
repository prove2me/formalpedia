-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertSpan.vec_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:15:50.708361+00:00
-- url     : https://prove2.me/submissions/326a6a12-27f0-464a-9471-77a888b20367

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases


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
theorem _root_.solution {f h : Fin (N + 2) → L} (h0 : f 0 = h 0) (hm : ∀ j, f (mid j) = h (mid j))
    (hl : f (Fin.last (N + 1)) = h (Fin.last (N + 1))) : f = h := by
  funext i
  rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
  · exact h0
  · exact hm j
  · exact hl
end GlobalTheory.CompanionTheory.InertSpan
