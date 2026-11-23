-- Prove2me | solution 1 for GlobalTheory.absNorm_inv_differentIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:50.478025+00:00
-- url     : https://prove2.me/submissions/da9451c2-309b-44fe-b576-c83be4c17130

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
    FractionalIdeal.absNorm (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
      = |(discr K : ℚ)|⁻¹ := by
  rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal K]
  simp
end GlobalTheory
