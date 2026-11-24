-- Prove2me | solution 1 for GlobalTheory.exists_nat_trace_of_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:50.347807+00:00
-- url     : https://prove2.me/submissions/b72624a9-22e3-4ac8-b50e-6d0bff085488

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {A : Type*} [Fintype A] [DecidableEq A]
namespace GlobalTheory
theorem _root_.solution {E : Matrix A A ℂ} (hE : E * E = E) :
    ∃ r : ℕ, E.trace = r := by
  have h : IsIdempotentElem (Matrix.toLin' E) := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hE]
  exact ⟨_, by rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ h).trace]⟩
end GlobalTheory
