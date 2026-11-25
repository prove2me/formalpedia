-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.hasSum_hurwitzCombTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:00.59561+00:00
-- url     : https://prove2.me/submissions/32cbecca-ab76-407f-a205-7ecafeb5c464

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
theorem _root_.solution {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ hurwitzCombTerm x n s) (hurwitzComb x s) := by
  have key : ∀ a : ℝ, a ∈ Icc (0 : ℝ) 1 →
      HasSum (fun n : ℕ ↦ (((n : ℝ) + a : ℝ) : ℂ) ^ (-s)) (hurwitzZeta a s) := by
    intro a ha
    refine (hasSum_hurwitzZeta_of_one_lt_re ha hs).congr_fun fun n ↦ ?_
    push_cast
    rw [cpow_neg, one_div]
  have h := ((key x ⟨hx0, hx1⟩).add ((key 1 ⟨zero_le_one, le_rfl⟩).mul_left ((1 - 2 * x : ℝ) : ℂ))).add
    ((key (1 / 2) ⟨by norm_num, by norm_num⟩).mul_left ((2 * x - 2 : ℝ) : ℂ))
  exact h
end GroundTheory.Global.Quadratic
