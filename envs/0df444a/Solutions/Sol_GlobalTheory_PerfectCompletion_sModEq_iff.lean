-- Prove2me | solution 1 for GlobalTheory.PerfectCompletion.sModEq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:22.775967+00:00
-- url     : https://prove2.me/submissions/788e03c2-28e8-496a-b2c7-63e320abe2b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PerfectCompletion
variable {V : Type} [CommRing V] (x : V)
namespace GlobalTheory.PerfectCompletion
theorem _root_.solution {C : Type} [CommRing C] (c : C) (n : ℕ) (u v : C) :
    u ≡ v [SMOD (Ideal.span {c} ^ n • ⊤ : Submodule C C)] ↔ c ^ n ∣ u - v := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
end GlobalTheory.PerfectCompletion
