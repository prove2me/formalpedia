-- Prove2me | solution 1 for GlobalTheory.T.trace_idempotent_not_divisible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:47.026861+00:00
-- url     : https://prove2.me/submissions/c72cbeb7-83c7-4477-b6e5-a21a7bba4d46

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_TraceIdempotentNotDivisible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_TraceIdempotentNotDivisibleStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_IdemTrace_not_dvd_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B) (p m : ℕ), p.Prime → Module.finrank ℤ B < p ^ m → x * x - x ∈ Ideal.span {((p : B)) ^ m} → x ∉ Ideal.span {((p : B)) ^ m} → ¬ ((p : ℤ) ^ m ∣ Algebra.trace ℤ B x) := by
  first | exact @GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace | exact GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace | (intros; apply GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace <;> assumption)
end _root_.GlobalTheory.T
