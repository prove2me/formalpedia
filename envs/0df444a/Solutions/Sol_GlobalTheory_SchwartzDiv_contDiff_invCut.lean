-- Prove2me | solution 1 for GlobalTheory.SchwartzDiv.contDiff_invCut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:42.814854+00:00
-- url     : https://prove2.me/submissions/8abb59bf-fa11-4152-bed2-b62a12c4ead4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
import Theorems.Thm_GlobalTheory_SchwartzDiv_invCut_of_le_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric
noncomputable section
open GlobalTheory GlobalTheory.SchwartzDiv
namespace GlobalTheory.SchwartzDiv
theorem _root_.solution : ContDiff ℝ ∞ invCut := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge 0 t with h | h
  · exact ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt).mul (contDiffAt_inv ℝ h.ne')
  · have : invCut =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show t < 1 / 2 by linarith)] with s hs
      exact invCut_of_le_half hs.le
    exact contDiffAt_const.congr_of_eventuallyEq this
end GlobalTheory.SchwartzDiv
