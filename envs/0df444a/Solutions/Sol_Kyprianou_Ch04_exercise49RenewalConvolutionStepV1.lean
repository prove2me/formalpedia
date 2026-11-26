-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RenewalConvolutionStepV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:37:18.592533+00:00
-- url     : https://prove2.me/submissions/d6968edb-073b-4183-baea-41ed197a7b4b

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal
set_option autoImplicit false
/-- Convolution distributes over the defective renewal equation. -/
theorem solution
    (rho : ℝ) (h0 : 0 ≤ rho) (h1 : rho < 1)
    (mu eta nu : Measure ℝ) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure eta] [IsProbabilityMeasure nu]
    (hLaw : mu = ENNReal.ofReal (1 - rho) • Measure.dirac 0 +
      ENNReal.ofReal rho • (mu.conv eta)) (B : Set ℝ) :
    (mu.conv nu B).toReal =
      (1 - rho) * (nu B).toReal + rho * (mu.conv (nu.conv eta) B).toReal := by
  have hc : mu.conv nu = ENNReal.ofReal (1 - rho) • nu +
      ENNReal.ofReal rho • (mu.conv (nu.conv eta)) := by
    have h := congrArg (fun m : Measure ℝ => m.conv nu) hLaw
    change mu.conv nu =
      (ENNReal.ofReal (1 - rho) • Measure.dirac 0 +
        ENNReal.ofReal rho • (mu.conv eta)).conv nu at h
    rw [Measure.add_conv, Measure.conv_smul_left, Measure.conv_smul_left,
      Measure.dirac_conv, Measure.conv_assoc, Measure.conv_comm eta nu] at h
    have hid : (fun y : ℝ => 0 + y) = id := funext zero_add
    rw [hid, Measure.map_id] at h
    exact h
  have h := congrArg (fun m : Measure ℝ => m B) hc
  change mu.conv nu B =
    (ENNReal.ofReal (1 - rho) • nu + ENNReal.ofReal rho • (mu.conv (nu.conv eta))) B at h
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply] at h
  change _ = ENNReal.ofReal (1 - rho) * nu B +
    ENNReal.ofReal rho * mu.conv (nu.conv eta) B at h
  have hA : ENNReal.ofReal (1 - rho) * nu B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top nu B)
  have hB : ENNReal.ofReal rho * mu.conv (nu.conv eta) B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top (mu.conv (nu.conv eta)) B)
  rw [h, ENNReal.toReal_add hA hB, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr h1.le), ENNReal.toReal_ofReal h0]
