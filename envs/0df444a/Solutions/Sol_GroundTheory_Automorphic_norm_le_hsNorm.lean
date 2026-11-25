-- Prove2me | solution 1 for GroundTheory.Automorphic.norm_le_hsNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:21.210464+00:00
-- url     : https://prove2.me/submissions/4156c324-7638-4127-9863-474c777b9900

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_hsNorm_nonneg
import Theorems.Thm_GroundTheory_Automorphic_enorm_apply_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  {L : Type*} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]
namespace GroundTheory.Automorphic
theorem _root_.solution {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) : ‖T‖ ≤ hsNorm T := by
  refine T.opNorm_le_bound (hsNorm_nonneg T) fun x => ?_
  have h := enorm_apply_sq_le T x
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_toReal hT.ne,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  rw [← Real.sqrt_sq (norm_nonneg (T x)), hsNorm, ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul ENNReal.toReal_nonneg]
  exact Real.sqrt_le_sqrt h
end GroundTheory.Automorphic
