-- Prove2me | solution 1 for GlobalTheory.AnisoSize.mul_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:54.212278+00:00
-- url     : https://prove2.me/submissions/16f1e57d-d7bb-4754-a2d2-62004a00bcbd

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
theorem _root_.solution {U x y : ℝ} {a b : ℕ} (hU : 2 ≤ U) (hx : x ≤ U ^ a) (hy : y ≤ U ^ b)
    (h0 : 0 ≤ y) : x * y ≤ U ^ (a + b) := by
  rw [pow_add]
  exact mul_le_mul hx hy h0 (by positivity)
end GlobalTheory.AnisoSize
