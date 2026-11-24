-- Prove2me | solution 1 for GlobalTheory.K5.Basic.not_isUnit_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:50.818395+00:00
-- url     : https://prove2.me/submissions/32561839-2b50-4617-bfc7-fc020b276720

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.K5.Basic
theorem _root_.solution : ¬ IsUnit (p : O0 p) := by
  intro h
  have h2 := h.map (AdicCompletion.evalₐ (pI p) 1)
  haveI : (pI p ^ 1).IsPrime := by
    rw [pow_one]; exact (Ideal.span_singleton_prime (prime_lau p).ne_zero).2 (prime_lau p)
  refine h2.ne_zero ?_
  rw [map_natCast, ← map_natCast (Ideal.Quotient.mk (pI p ^ 1)), Ideal.Quotient.eq_zero_iff_mem,
    pow_one]
  exact Ideal.mem_span_singleton_self _
end GlobalTheory.K5.Basic
