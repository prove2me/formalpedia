-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneCanonicalScalePositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:28:24.5202+00:00
-- url     : https://prove2.me/submissions/9013ffc7-348d-4704-a766-50dc14755e90

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneGammaRecurrence
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Set
set_option autoImplicit false

theorem solution
    (alpha cpos cneg : ℝ)
    (ha1 : 1 < alpha) (ha2 : alpha < 2)
    (hsum : 0 < cpos + cneg) :
    0 < -Real.Gamma (-alpha) *
      Real.cos (Real.pi * alpha / 2) * (cpos + cneg) := by
  have hg2 : 0 < Real.Gamma (2 - alpha) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hrec1 : Real.Gamma (2 - alpha) =
      (1 - alpha) * Real.Gamma (1 - alpha) := by
    convert Real.Gamma_add_one (s := 1 - alpha) (by linarith) using 1 <;> ring
  have hg1 : Real.Gamma (1 - alpha) < 0 := by
    by_contra hn
    have hh : 0 ≤ Real.Gamma (1 - alpha) := le_of_not_gt hn
    have h : (1 - alpha) * Real.Gamma (1 - alpha) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hh
    linarith
  have hrec2 :=
    Kyprianou.Ch01.stableAlphaAboveOneGammaRecurrence alpha ha1 ha2
  have hg0 : 0 < Real.Gamma (-alpha) := by
    by_contra hn
    have hh : Real.Gamma (-alpha) ≤ 0 := le_of_not_gt hn
    have h : 0 ≤ -alpha * Real.Gamma (-alpha) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hh
    linarith
  have hp : 0 < Real.pi := Real.pi_pos
  have hp1 : Real.pi / 2 < Real.pi * alpha / 2 := by
    nlinarith [mul_lt_mul_of_pos_left ha1 hp]
  have hp2 : Real.pi * alpha / 2 < Real.pi + Real.pi / 2 := by
    nlinarith [mul_lt_mul_of_pos_left ha2 hp]
  have hc : Real.cos (Real.pi * alpha / 2) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hp1 hp2
  exact mul_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hg0) hc) hsum
