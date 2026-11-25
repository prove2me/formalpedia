-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.differentiableOn_tsum_hurwitzCombTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:59.876922+00:00
-- url     : https://prove2.me/submissions/86024a00-4926-4894-bc0a-474251323d4f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
import Theorems.Thm_GroundTheory_Global_Quadratic_norm_hurwitzCombTerm_le
import Theorems.Thm_GroundTheory_Global_Quadratic_summable_hurwitzCombBound

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
    DifferentiableOn ℂ (fun s ↦ ∑' n, hurwitzCombTerm x n s) (Metric.ball 1 (3 / 2)) := by
  refine differentiableOn_tsum_of_summable_norm (summable_hurwitzCombBound (lt_min hx0 (by norm_num)))
    (fun n ↦ ?_) Metric.isOpen_ball (fun n s hs ↦ norm_hurwitzCombTerm_le hx0 hx1 n hs)
  have hd : ∀ a : ℝ, 0 < (n : ℝ) + a →
      Differentiable ℂ (fun s : ℂ ↦ (((n : ℝ) + a : ℝ) : ℂ) ^ (-s)) := fun a ha s ↦
    differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.2 ha.ne'))
  have hpos : ∀ a : ℝ, 0 < a → 0 < (n : ℝ) + a := fun a ha ↦
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha
  exact (((hd x (hpos x hx0)).add ((hd 1 (hpos 1 one_pos)).const_mul _)).add
    ((hd (1 / 2) (hpos _ (by norm_num))).const_mul _)).differentiableOn
end GroundTheory.Global.Quadratic
