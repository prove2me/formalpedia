-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCount.trace_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:06:31.875414+00:00
-- url     : https://prove2.me/submissions/29e5d9dc-989a-490a-879f-b4a393ebcd51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CountOfHeisenbergIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCount
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L} {σ : L →+* L} {q N : ℕ}
namespace GlobalTheory.CompanionTheory.InertCount
theorem _root_.solution (hH : Heis) (hU : IsUnramInv ϖ σ q) {w : GU σ (N + 2)} (hw : w ∈ radQ σ N)
    (h0 : rowOf w = 0) : σ (cornerOf w) + cornerOf w = 0 := by
  have h := ((hH L ϖ σ q N hU).1 w hw).2.1
  rw [h0, zero_dotProduct] at h
  rw [add_comm]
  exact h
end GlobalTheory.CompanionTheory.InertCount
