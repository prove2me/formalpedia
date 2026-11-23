-- Prove2me | solution 1 for GlobalTheory.AnisoSize.add_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:03.825049+00:00
-- url     : https://prove2.me/submissions/7f8e93fe-6bfa-43b0-969d-c82976914371

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize
namespace GlobalTheory.AnisoSize
theorem _root_.solution {U x y : ℝ} {a b : ℕ} (hU : 2 ≤ U) (hx : x ≤ U ^ a) (hy : y ≤ U ^ b) :
    x + y ≤ U ^ (max a b + 1) := by
  have h1 := hx.trans (pow_le_pow_right₀ (by linarith) (le_max_left a b))
  have h2 := hy.trans (pow_le_pow_right₀ (by linarith) (le_max_right a b))
  have h3 : 0 ≤ U ^ max a b := by positivity
  rw [pow_succ]
  nlinarith
end GlobalTheory.AnisoSize
