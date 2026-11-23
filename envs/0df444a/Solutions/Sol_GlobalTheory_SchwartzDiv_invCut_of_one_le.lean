-- Prove2me | solution 1 for GlobalTheory.SchwartzDiv.invCut_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:22.501831+00:00
-- url     : https://prove2.me/submissions/50c6b499-bae0-40c4-80fd-52aa68cb6bf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition

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
theorem _root_.solution {t : ℝ} (ht : 1 ≤ t) : invCut t = t⁻¹ := by
  rw [invCut, Real.smoothTransition.one_of_one_le (by linarith), one_mul]
end GlobalTheory.SchwartzDiv
