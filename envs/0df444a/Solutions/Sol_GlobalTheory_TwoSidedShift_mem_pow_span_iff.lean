-- Prove2me | solution 1 for GlobalTheory.TwoSidedShift.mem_pow_span_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:42:25.949201+00:00
-- url     : https://prove2.me/submissions/f7573549-c412-45b0-b590-4c66178c0e27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwoSidedShiftSeriesHasSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TwoSidedShift
namespace GlobalTheory.TwoSidedShift
theorem _root_.solution (l : ℕ) (A : Type) [CommRing A] (n : ℕ) (x : A) :
    x ∈ ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A A) ↔ (l : A) ^ n ∣ x := by
  simp [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
end GlobalTheory.TwoSidedShift
