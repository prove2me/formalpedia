-- Prove2me | solution 1 for GlobalTheory.FixedPointApproximation.smodEq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:11:17.373201+00:00
-- url     : https://prove2.me/submissions/f51c2533-869f-481a-a602-b482fc21254c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ApproxStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FixedPointApproximation
namespace GlobalTheory.FixedPointApproximation
theorem _root_.solution {B : Type} [CommRing B] (q : B) (n : ℕ) (x y : B) :
    x ≡ y [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule B B)] ↔ q ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
end GlobalTheory.FixedPointApproximation
