-- Prove2me | solution 1 for GlobalTheory.PerfectCompletion.dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:21.005484+00:00
-- url     : https://prove2.me/submissions/dce6d7eb-8fdb-4649-a58e-3c45cca725e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfect
import Theorems.Thm_GlobalTheory_PerfectCompletion_eval_eq_zero_iff

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
theorem _root_.solution (s : V) (r : ℕ) :
    (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r ∣ algebraMap V _ s ↔ x ^ r ∣ s := by
  rw [← eval_eq_zero_iff]
  have : AdicCompletion.eval (Ideal.span {x}) V r (algebraMap V _ s) =
      Submodule.Quotient.mk s := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
end GlobalTheory.PerfectCompletion
