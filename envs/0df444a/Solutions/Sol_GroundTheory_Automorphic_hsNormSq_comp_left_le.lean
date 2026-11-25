-- Prove2me | solution 1 for GroundTheory.Automorphic.hsNormSq_comp_left_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:57.895915+00:00
-- url     : https://prove2.me/submissions/0e68b3ad-2292-471b-8ace-3805842d2a97

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Theorems.Thm_GroundTheory_Automorphic_enorm_apply_le

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
theorem _root_.solution (A : K →L[𝕜] L) (T : H →L[𝕜] K) :
    hsNormSq (A.comp T) ≤ ‖A‖ₑ ^ 2 * hsNormSq T := by
  simp only [hsNormSq, ← ENNReal.tsum_mul_left, comp_apply]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← mul_pow]
  gcongr
  exact enorm_apply_le _ _
end GroundTheory.Automorphic
