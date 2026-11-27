-- Prove2me | solution 1 for GlobalTheory.trace_mem_of_mem_dual_spanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:27.206876+00:00
-- url     : https://prove2.me/submissions/6f471415-f6e2-4467-b860-fe45e962cbfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_trace_mem_of_mem_traceDual

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
    (hx : x ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (q : K))) :
    ∃ m : ℤ, Algebra.trace ℚ K x = q⁻¹ * m := by
  refine trace_mem_of_mem_traceDual hq ?_
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual ℤ ℚ
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (by exact_mod_cast hq)),
    FractionalIdeal.coe_spanSingleton] at hx
  exact hx
end GlobalTheory
