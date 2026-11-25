-- Prove2me | solution 1 for GroundTheory.Automorphic.enorm_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:00.938583+00:00
-- url     : https://prove2.me/submissions/4af14c3b-8d02-4330-86e4-c38d6dda18eb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt

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
theorem _root_.solution (A : H →L[𝕜] K) (x : H) : ‖A x‖ₑ ≤ ‖A‖ₑ * ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (A.le_opNorm x)
end GroundTheory.Automorphic
