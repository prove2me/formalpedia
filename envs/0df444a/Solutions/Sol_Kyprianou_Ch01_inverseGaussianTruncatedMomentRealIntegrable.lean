-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianTruncatedMomentRealIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T01:02:43.7382+00:00
-- url     : https://prove2.me/submissions/632b0929-e7ef-41ad-9787-c32f1f2137b8

import Mathlib
import Mathlib.Tactic.FunProp
import Theorems.Thm_Kyprianou_Ch01_stableGammaPowerEnvelopeIntegrable
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianTruncatedMomentEnvelopeBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Inverse Gaussian truncated moment integrability by the power envelope. -/
theorem solution (b : ℝ) (hb : 0 < b) :
    IntegrableOn
      (fun x : ℝ =>
        (min 1 (x ^ 2)) *
          ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
            Real.exp (-(b ^ 2 * x / 2))))
      (Set.Ioi (0 : ℝ)) volume := by
  have henv0 := Kyprianou.Ch01.stableGammaPowerEnvelopeIntegrable
    (1 / 2 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num)
  have henv : IntegrableOn
      (fun x : ℝ => if x ≤ 1 then x ^ (-(1 / 2 : ℝ))
        else x ^ (-(3 / 2 : ℝ))) (Set.Ioi (0 : ℝ)) := by
    have hscaled : IntegrableOn
        (fun x : ℝ => if x ≤ 1 then
          1 * x ^ (-(1 / 2 : ℝ))
          else x ^ (-(1 / 2 : ℝ) - 1))
        (Set.Ioi (0 : ℝ)) := henv0
    refine hscaled.congr_fun (fun x hx => ?_) measurableSet_Ioi
    by_cases h : x ≤ 1
    · simp [h]
    · simp only [if_neg h]
      congr 1
      ring
  apply Integrable.mono' henv
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hbound :=
      Kyprianou.Ch01.inverseGaussianTruncatedMomentEnvelopeBound b x hb hx
    have hnonneg : 0 ≤
        (min 1 (x ^ 2)) *
          ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
            Real.exp (-(b ^ 2 * x / 2))) := by
      positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound
