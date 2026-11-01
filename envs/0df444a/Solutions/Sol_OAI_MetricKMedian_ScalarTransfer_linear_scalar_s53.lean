-- Prove2me | solution 1 for OAI.MetricKMedian.ScalarTransfer.linear_scalar_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:18:25.715004+00:00
-- url     : https://prove2.me/submissions/4f0a25da-c9ed-49a2-8033-61feff5e6a94

import Mathlib
import Definitions.Def_OAIQ053K027

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_NormalizedTransfer
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

private theorem Q0_difference (p a k w W : ℝ) (s : Bool) :
    Q0 p a k w s-Q0 p a k W s =
      p*hh s*((w-uZero s)^2-(W-uZero s)^2) := by
  cases s <;> norm_num [Q0, hh, uZero, d] <;> ring

theorem Q0_minimum {p a k x w : ℝ} (hp0 : 0 ≤ p)
    (hw : w ≤ 1-x) (s : Bool) :
    Q0 p a k (if s then uZero s else min (1-x) (uZero s)) s ≤ Q0 p a k w s := by
  have hsq : ((if s then uZero s else min (1-x) (uZero s))-uZero s)^2 ≤ (w-uZero s)^2 := by
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hcut : 1-x ≤ uZero false
      · rw [min_eq_left hcut]
        nlinarith only [hw, hcut, sq_nonneg (w-(1-x))]
      · rw [min_eq_right (le_of_not_ge hcut), sub_self, zero_pow (by decide : 2 ≠ 0)]
        exact sq_nonneg _
    · simpa only [↓reduceIte, sub_self, zero_pow (by decide : 2 ≠ 0)] using sq_nonneg (w-uZero true)
  have hh0 : 0 ≤ hh s := by cases s <;> norm_num [hh, d]
  have hp := mul_nonneg (mul_nonneg hp0 hh0) (sub_nonneg.mpr hsq)
  rw [←Q0_difference] at hp
  linarith only [hp]

private theorem linear_gap_identity (p a k x w r : ℝ) (s : Bool) :
    stdK p k x w r s-d s*(stdM p a w r s-stdL p a x w r s) =
      (1-r)*Q0 p a k w s+r*(Q1 p a k x s+hh s*p*(w-uOne s)^2) := by
  dsimp only [stdK, stdM, stdL, stdB, Q0, Q1, N, c, ell, uOne, hh]
  cases s <;> norm_num [bit, d] <;> ring

theorem linear_scalar_s53_oai {p a k x w r : ℝ} (hp0 : 0 ≤ p) (hw : w ≤ 1-x)
    (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool)
    (hQ0 : 0 ≤ Q0 p a k (if s then uZero s else min (1-x) (uZero s)) s)
    (hQ1 : 0 ≤ Q1 p a k x s) :
    d s*(stdM p a w r s-stdL p a x w r s) ≤ stdK p k x w r s := by
  have hzero := hQ0.trans (Q0_minimum hp0 hw s)
  have hh0 : 0 ≤ hh s := by cases s <;> norm_num [hh, d]
  have hone : 0 ≤ Q1 p a k x s+hh s*p*(w-uOne s)^2 := by positivity
  have hn := add_nonneg (mul_nonneg (sub_nonneg.mpr hr) hzero) (mul_nonneg hr0 hone)
  rw [←linear_gap_identity] at hn
  exact sub_nonneg.mp hn

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.ScalarTransfer.linear_scalar_s53_oai := @OAI.MetricKMedian.ScalarTransfer.linear_scalar_s53_oai
