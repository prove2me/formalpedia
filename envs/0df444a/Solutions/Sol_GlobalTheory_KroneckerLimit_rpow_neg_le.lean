-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.rpow_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:35.241075+00:00
-- url     : https://prove2.me/submissions/3dbac344-4cac-4bd3-b075-ce81b7d262da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution {r s : ℝ} (hr : 0 < r) (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    r ^ (-s) ≤ r ^ (-1 : ℝ) + r ^ (-2 : ℝ) := by
  have p1 : 0 ≤ r ^ (-1 : ℝ) := by positivity
  have p2 : 0 ≤ r ^ (-2 : ℝ) := by positivity
  rcases le_total r 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge hr h (show (-2 : ℝ) ≤ -s by linarith)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h (show -s ≤ (-1 : ℝ) by linarith)
    linarith
end GlobalTheory.KroneckerLimit
