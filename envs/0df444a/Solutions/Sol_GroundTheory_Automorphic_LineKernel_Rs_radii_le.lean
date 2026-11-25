-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.Rs_radii_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:00.026809+00:00
-- url     : https://prove2.me/submissions/395f10fb-cf3b-4a42-a4a1-d92d0234f144

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (n : ℕ) : Rs (radii ε) n ≤ ε / 2 := by
  have e : ∀ j, 2 * radii ε j = ε / 4 * (1 / 2) ^ j := by
    intro j; unfold radii; rw [pow_add, one_div_pow]; field_simp; norm_num
  unfold Rs
  simp_rw [e, ← Finset.mul_sum]
  have := sum_geometric_two_le (n + 1)
  nlinarith
end GroundTheory.Automorphic.LineKernel
