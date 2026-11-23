-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.summable_zero_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:37.596946+00:00
-- url     : https://prove2.me/submissions/4eeddaa4-919c-4a07-bf21-00ab2be82cf2

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
theorem _root_.solution {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun n : ℤ => (((0 : ℝ) + n) ^ 2 + 0 ^ 2) ^ (-s)) := by
  refine (Real.summable_abs_int_rpow (b := 2 * s) (by linarith)).congr fun n => ?_
  rw [show -(2 * s) = ((2 : ℕ) : ℝ) * (-s) by push_cast; ring, Real.rpow_natCast_mul (abs_nonneg _)]
  simp
end GlobalTheory.KroneckerLimit
