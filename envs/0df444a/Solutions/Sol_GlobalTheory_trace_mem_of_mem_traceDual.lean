-- Prove2me | solution 1 for GlobalTheory.trace_mem_of_mem_traceDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:51:34.972632+00:00
-- url     : https://prove2.me/submissions/878e3872-a191-4a58-9745-8318da69e3d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_exists_int_eq_mul_trace_of_mem_traceDual

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
theorem _root_.solution {q : ℚ} (hq : q ≠ 0) {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (Submodule.span (𝓞 K) {(q : K)})) :
    ∃ m : ℤ, Algebra.trace ℚ K x = q⁻¹ * m := by
  obtain ⟨m, hm⟩ := exists_int_eq_mul_trace_of_mem_traceDual hx
  exact ⟨m, by rw [← hm, inv_mul_cancel_left₀ hq]⟩
end GlobalTheory
