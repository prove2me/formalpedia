-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianJumpPowerEnvelopeIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:11:07.068187+00:00
-- url     : https://prove2.me/submissions/9e6dc368-83cd-4bb8-978d-e3fd8560e84b

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaPowerEnvelopeIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Positive-half-line inverse Gaussian Fourier envelope is Lebesgue integrable. -/
theorem solution (theta : ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        (|theta| + 2) *
          (if x ≤ 1 then x ^ (-(1 / 2 : ℝ))
            else x ^ (-(3 / 2 : ℝ))))
      (Set.Ioi (0 : ℝ)) volume := by
  have hbase := Kyprianou.Ch01.stableGammaPowerEnvelopeIntegrable
    (1 / 2 : ℝ) 1 (by norm_num) (by norm_num) (by norm_num)
  have hscaled : IntegrableOn
      (fun x : ℝ => (|theta| + 2) *
        (if x ≤ 1 then 1 * x ^ (-(1 / 2 : ℝ))
          else x ^ (-(1 / 2 : ℝ) - 1)))
      (Set.Ioi (0 : ℝ)) volume :=
    hbase.const_mul (|theta| + 2)
  refine hscaled.congr_fun (fun x hx => ?_) measurableSet_Ioi
  by_cases h : x ≤ 1
  · simp [h]
  · simp only [if_neg h]
    congr 1
    ring
