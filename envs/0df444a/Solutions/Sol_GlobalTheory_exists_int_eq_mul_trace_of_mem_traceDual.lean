-- Prove2me | solution 1 for GlobalTheory.exists_int_eq_mul_trace_of_mem_traceDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:42:34.66492+00:00
-- url     : https://prove2.me/submissions/3534df52-b6a8-4630-bb0c-873c0dd3b12d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution {q : ℚ} {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (Submodule.span (𝓞 K) {(q : K)})) :
    ∃ m : ℤ, q * Algebra.trace ℚ K x = m := by
  obtain ⟨m, hm⟩ := Submodule.mem_traceDual.mp hx q (Submodule.mem_span_singleton_self _)
  refine ⟨m, ?_⟩
  rw [Algebra.traceForm_apply, mul_comm, ← Rat.smul_def, map_smul, smul_eq_mul, eq_intCast] at hm
  exact hm.symm
end GlobalTheory
