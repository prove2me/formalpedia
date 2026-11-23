-- Prove2me | solution 1 for Kyprianou.Ch01.summablePowerSeriesZeroCoefficientsOfSmallPositiveValues
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:33:56.529776+00:00
-- url     : https://prove2.me/submissions/b8aa3666-d7c8-4919-9919-69c4c95923b5

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_Kyprianou_Ch01_summableRealSequenceBounded
import Theorems.Thm_Kyprianou_Ch01_smallPositivePowerSeriesCoefficientBound
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
set_option autoImplicit false

theorem solution
    (a : ℕ → ℝ) (hsum : Summable a)
    (h : ∀ z : ℝ, 0 < z → z ≤ (1/2 : ℝ) →
        HasSum (fun k : ℕ => z ^ k * a k) 0) :
    ∀ k, a k = 0 := by
  obtain ⟨M, hM0, hM⟩ :=
    Kyprianou.Ch01.summableRealSequenceBounded a hsum
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have key : ∀ z : ℝ, 0 < z → z ≤ (1/2 : ℝ) →
        |a k| ≤ 2 * M * z := by
      intro z hz hz2
      exact Kyprianou.Ch01.smallPositivePowerSeriesCoefficientBound
        a M hM0 hM h k (fun i hi => ih i hi) z hz hz2
    by_contra hne
    have ht : 0 < |a k| := abs_pos.mpr hne
    set z := min (1/2 : ℝ) (|a k| / (4 * M + 4)) with hzdef
    have hz : 0 < z := lt_min (by norm_num) (div_pos ht (by linarith))
    have hz2 : z ≤ 1/2 := min_le_left _ _
    have hz3 : z ≤ |a k| / (4 * M + 4) := min_le_right _ _
    have := key z hz hz2
    have h4 : z * (4 * M + 4) ≤ |a k| := by rwa [le_div_iff₀ (by linarith)] at hz3
    nlinarith

