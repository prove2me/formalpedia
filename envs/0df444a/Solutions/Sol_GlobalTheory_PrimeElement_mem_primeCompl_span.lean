-- Prove2me | solution 1 for GlobalTheory.PrimeElement.mem_primeCompl_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:13.043242+00:00
-- url     : https://prove2.me/submissions/6dd46e1f-81a5-44fa-86a1-b46a0482fbe6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PrimeElement
variable {R : Type*} [CommRing R] {π : R}
namespace GlobalTheory.PrimeElement
theorem _root_.solution [(Ideal.span {π}).IsPrime] {b : R} :
    b ∈ (Ideal.span {π}).primeCompl ↔ ¬ π ∣ b := by
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
end GlobalTheory.PrimeElement
