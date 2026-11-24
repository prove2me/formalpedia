-- Prove2me | solution 1 for GlobalTheory.ValCompletion.algebraMap_pow_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:13.754964+00:00
-- url     : https://prove2.me/submissions/91ebd539-4537-4dcb-a2a2-4e50f4086d51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDoma
import Theorems.Thm_P2M_GlobalTheory_ValCompletion_eval__algebraMap_9fca5057166d
import Theorems.Thm_GlobalTheory_ValCompletion_not_pow_succ_dvd_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.ValCompletion
variable {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] {x : V}
namespace GlobalTheory.ValCompletion
theorem _root_.solution (hx0 : x ≠ 0) (hxu : ¬ IsUnit x) (m : ℕ) : (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ m ≠ 0 := by
  intro h
  have h2 := congrArg (AdicCompletion.evalₐ (Ideal.span {x}) (m + 1)) h
  rw [← map_pow, evalₐ_algebraMap, map_zero, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  exact not_pow_succ_dvd_pow hx0 hxu m h2
end GlobalTheory.ValCompletion
