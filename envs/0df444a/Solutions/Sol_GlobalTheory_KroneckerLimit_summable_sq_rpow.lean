-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.summable_sq_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:35.466615+00:00
-- url     : https://prove2.me/submissions/5fccf144-e8b8-4705-bb52-0f033b834a15

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
theorem _root_.solution {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) :
    Summable fun m : ℕ => (((m + 1) * y) ^ 2) ^ (-s) := by
  have := ((summable_nat_add_iff 1).2
    (Real.summable_nat_rpow.2 (show -(2 * s) < -1 by linarith))).mul_right ((y ^ 2) ^ (-s))
  refine this.congr fun m => ?_
  rw [mul_pow, Real.mul_rpow (by positivity) (by positivity),
    show -(2 * s) = ((2 : ℕ) : ℝ) * (-s) by push_cast; ring, Real.rpow_natCast_mul (by positivity)]
  push_cast
  rfl
end GlobalTheory.KroneckerLimit
