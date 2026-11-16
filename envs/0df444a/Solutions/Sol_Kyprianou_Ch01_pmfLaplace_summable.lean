-- Prove2me | solution 1 for Kyprianou.Ch01.pmfLaplace_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:24:33.271004+00:00
-- url     : https://prove2.me/submissions/6c6f4f74-8bae-475a-be4f-751465a306d2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Positive exponential weights are summable under every probability mass function. -/
theorem solution (p : PMF ℕ) (q : ℝ) (hq : 0 ≤ q) :
    Summable (fun k : ℕ => (p k).toReal * Real.exp (-q * (k : ℝ))) := by
  have hp : Summable (fun k : ℕ => (p k).toReal) :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  apply hp.of_norm_bounded
  intro k
  have hweight : Real.exp (-q * (k : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (ENNReal.toReal_nonneg), abs_of_pos (Real.exp_pos _)]
  calc
    (p k).toReal * Real.exp (-q * (k : ℝ)) ≤ (p k).toReal * 1 :=
      mul_le_mul_of_nonneg_left hweight ENNReal.toReal_nonneg
    _ = (p k).toReal := mul_one _
