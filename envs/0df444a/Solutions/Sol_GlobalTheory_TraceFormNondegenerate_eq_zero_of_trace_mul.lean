-- Prove2me | solution 1 for GlobalTheory.TraceFormNondegenerate.eq_zero_of_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:39:08.961047+00:00
-- url     : https://prove2.me/submissions/66674128-46cd-4353-95a2-e944c360f21a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanEqTopOfTraceEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceFormNondegenerate
namespace GlobalTheory.TraceFormNondegenerate
theorem _root_.solution {K : Type} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K)
    (h : ∀ Y : Matrix (Fin n) (Fin n) K, Matrix.trace (X * Y) = 0) : X = 0 := by
  ext i j
  have hij := h (Matrix.single j i 1)
  rw [Matrix.trace_mul_single] at hij
  simpa using hij
end GlobalTheory.TraceFormNondegenerate
