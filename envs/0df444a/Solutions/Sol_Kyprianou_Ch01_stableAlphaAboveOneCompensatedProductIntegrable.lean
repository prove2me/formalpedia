-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneCompensatedProductIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:19:46.810666+00:00
-- url     : https://prove2.me/submissions/07ac491e-63b7-4dbf-ba16-dae29469ce2f

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

/-- Integrability of exactly the compensated numerator times its real power. -/
theorem solution (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) *
            (((r ^ (-(alpha + 1)) : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have h := Kyprianou.Ch01.stableAlphaAboveOneKernelIntegrable
    alpha ha1 ha2
  apply (integrableOn_congr_fun (fun r hr => ?_) measurableSet_Ioi).mpr h
  rw [div_eq_mul_inv]
  congr 1
  rw [Real.rpow_neg hr.le]
  norm_cast
