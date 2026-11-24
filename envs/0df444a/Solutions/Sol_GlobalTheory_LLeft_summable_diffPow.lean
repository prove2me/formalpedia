-- Prove2me | solution 1 for GlobalTheory.LLeft.summable_diffPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:27:12.360838+00:00
-- url     : https://prove2.me/submissions/4379ed65-fbb9-4180-8194-5d4f0617afe1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
import Theorems.Thm_GlobalTheory_LLeft_norm_diffPow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft
namespace GlobalTheory.LLeft
theorem _root_.solution (k : ℕ) (s : ℂ) (hs : 1 < s.re + k) :
    Summable (fun n : ℕ => ‖diffPow k s ((n : ℝ) + 1)‖) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re + k))) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr
      (show -(s.re + k) < -1 by linarith))
    simpa using this
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => norm_diffPow_le k s _ (by positivity) (by linarith)) (h.mul_left _)
end GlobalTheory.LLeft
