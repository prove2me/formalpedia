-- Prove2me | solution 1 for GlobalTheory.SchwartzDiv.invCut_of_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:22.505953+00:00
-- url     : https://prove2.me/submissions/bd2fd695-6a5a-43e1-a89e-273417b33e42

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
theorem _root_.solution {t : ℝ} (ht : t ≤ 1 / 2) : invCut t = 0 := by
  rw [invCut, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
end GlobalTheory.SchwartzDiv
