-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseKernelMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:40:55.286966+00:00
-- url     : https://prove2.me/submissions/bd1103e7-5d59-4a1e-a8c2-92a645f5933d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real Complex
set_option autoImplicit false
/-! Exact measurability of the compensated stable kernel with the source cutoff. -/
theorem solution (z : ℝ) :
    Measurable (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
  have hm : Measurable (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
      have hCutMeas : Measurable
          (fun x : ℝ => if x < 1 then (1 : ℂ) else 0) :=
        Measurable.ite measurableSet_Iio measurable_const measurable_const
      have hExpMeas : Measurable
          (fun x : ℝ => Complex.exp (Complex.I * (((z * x : ℝ) : ℂ)))) := by
        fun_prop
      have hLinearMeas : Measurable
          (fun x : ℝ => Complex.I * (((z * x : ℝ) : ℂ))) := by
        fun_prop
      have hDenMeas : Measurable
          (fun x : ℝ => ((((x : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
        fun_prop
      exact ((measurable_const.sub hExpMeas).add
        (hLinearMeas.mul hCutMeas)).div hDenMeas
  exact hm
