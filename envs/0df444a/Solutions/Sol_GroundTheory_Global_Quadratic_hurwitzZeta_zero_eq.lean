-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.hurwitzZeta_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:12.97379+00:00
-- url     : https://prove2.me/submissions/f62200fe-0722-4208-b6c6-625e7d8addf1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
import Theorems.Thm_GroundTheory_Global_Quadratic_tsum_hurwitzCombTerm_eq
import Theorems.Thm_GroundTheory_Global_Quadratic_hurwitzZeta_one_zero
import Theorems.Thm_GroundTheory_Global_Quadratic_hurwitzZeta_half_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - x := by
  have hterm : ∀ n : ℕ, hurwitzCombTerm x n 0 = 0 := fun n ↦ by
    simp only [hurwitzCombTerm, neg_zero, cpow_zero, mul_one]
    push_cast
    ring
  have h0 : hurwitzComb x 0 = 0 := by
    rw [← tsum_hurwitzCombTerm_eq hx0 hx1 (s := 0) (by
      rw [Metric.mem_ball, dist_eq_norm, zero_sub, norm_neg, norm_one]; norm_num)]
    simp [hterm]
  simp only [hurwitzComb, hurwitzZeta_one_zero, hurwitzZeta_half_zero] at h0
  push_cast at h0
  linear_combination h0
end GroundTheory.Global.Quadratic
