-- Prove2me | solution 1 for GlobalTheory.trace_eq_sum_realEmbeddings
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:13.089422+00:00
-- url     : https://prove2.me/submissions/43b0ed75-102d-4966-9611-2751bc230c29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_trace_eq_sum_complexEmbeddings
import Theorems.Thm_GlobalTheory_bijective_ofRealHom_comp

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
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory
theorem _root_.solution (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ σ : F →+* ℝ, σ x := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, trace_eq_sum_complexEmbeddings, Complex.ofReal_sum]
  exact ((bijective_ofRealHom_comp F).sum_comp (fun φ => φ x)).symm
end GlobalTheory
