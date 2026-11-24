-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.rowSum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:12:02.935006+00:00
-- url     : https://prove2.me/submissions/eaf85d08-e3b4-4d88-9301-0135e2576d47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_integrable_rpow_sq_add
import Theorems.Thm_GlobalTheory_KroneckerLimit_integral_rpow_sq_add
import Theorems.Thm_GlobalTheory_KroneckerLimit_summable_and_abs_tsum_sub_integral_le


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
theorem _root_.solution (a : ℝ) {Y s : ℝ} (hY : 0 < Y) (hs : 1 ≤ s) :
    Summable (fun n : ℤ => ((a + n) ^ 2 + Y ^ 2) ^ (-s)) ∧
      |rowSum a Y s - betaConst s * Y ^ (1 - 2 * s)| ≤ (Y ^ 2) ^ (-s) := by
  have := summable_and_abs_tsum_sub_integral_le (f := fun t : ℝ => (t ^ 2 + Y ^ 2) ^ (-s))
    (fun t => by positivity)
    (Continuous.rpow_const (by fun_prop) fun t => Or.inl (by positivity))
    (fun u (hu : u ≤ 0) v (hv : v ≤ 0) huv => Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith) (by linarith))
    (fun u (hu : 0 ≤ u) v (hv : 0 ≤ v) huv => Real.rpow_le_rpow_of_nonpos (by positivity)
      (by nlinarith) (by linarith))
    (integrable_rpow_sq_add hY hs) a
  rw [integral_rpow_sq_add hY (by linarith)] at this
  simpa [rowSum] using this
end GlobalTheory.KroneckerLimit
