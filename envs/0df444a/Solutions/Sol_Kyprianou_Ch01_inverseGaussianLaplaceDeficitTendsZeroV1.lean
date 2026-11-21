-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianLaplaceDeficitTendsZeroV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:15:31.293914+00:00
-- url     : https://prove2.me/submissions/8fe62b65-d348-484b-a24d-0b1ff5921326

import Mathlib
open Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem solution
    (b : ℝ) :
    Tendsto
      (fun s : ℝ≥0 =>
        1 - Real.exp (-((s : ℝ) * (Real.sqrt (b ^ 2 + 2) - b))))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  have hMul : Continuous (fun s : ℝ≥0 =>
      (s : ℝ) * (Real.sqrt (b ^ 2 + 2) - b)) :=
    NNReal.continuous_coe.mul continuous_const
  have hExp : Continuous (fun s : ℝ≥0 =>
      Real.exp (-((s : ℝ) * (Real.sqrt (b ^ 2 + 2) - b)))) :=
    Real.continuous_exp.comp hMul.neg
  have hCont : Continuous (fun s : ℝ≥0 =>
      1 - Real.exp (-((s : ℝ) * (Real.sqrt (b ^ 2 + 2) - b)))) :=
    continuous_const.sub hExp
  simpa using (hCont.continuousAt (x := (0 : ℝ≥0))).tendsto
