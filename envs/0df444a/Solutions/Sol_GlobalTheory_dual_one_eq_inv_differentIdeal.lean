-- Prove2me | solution 1 for GlobalTheory.dual_one_eq_inv_differentIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:01.090588+00:00
-- url     : https://prove2.me/submissions/1f7ef7d6-5f6d-46dc-a9c4-8c39355ed824

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
variable (K)
namespace GlobalTheory
theorem _root_.solution :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
end GlobalTheory
