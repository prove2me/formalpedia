-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.summable_hurwitzCombBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:03.901078+00:00
-- url     : https://prove2.me/submissions/a784b0b5-340b-4a90-8698-3823fb5f1bfd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero

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
theorem _root_.solution {x₀ : ℝ} (hx₀ : 0 < x₀) :
    Summable (fun n : ℕ ↦ 18 * (((n : ℝ) + x₀) ^ (-(3 / 2) : ℝ) + ((n : ℝ) + x₀) ^ (-(9 / 2) : ℝ))) := by
  have key : ∀ p : ℝ, 1 < p → Summable (fun n : ℕ ↦ ((n : ℝ) + x₀) ^ (-p)) := by
    intro p hp
    refine ((Real.summable_one_div_nat_add_rpow x₀ p).2 hp).congr fun n ↦ ?_
    have h : 0 < (n : ℝ) + x₀ := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) hx₀
    rw [abs_of_pos h, Real.rpow_neg h.le, one_div]
  exact ((key _ (by norm_num)).add (key _ (by norm_num))).mul_left 18
end GroundTheory.Global.Quadratic
