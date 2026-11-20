-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneDerivativeProductIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:29:10.483173+00:00
-- url     : https://prove2.me/submissions/f710e85c-fc38-46f2-8294-25c1f62d4279

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneReducedFourierIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

/-- Reduced Fourier kernel integrability is stable under its exact complex coefficient. -/
theorem solution (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hα : (alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one ha1))
  have h := Kyprianou.Ch01.stableAlphaAboveOneReducedFourierIntegrable
    alpha ha1 ha2
  have hs := h.const_mul (-(Complex.I / (alpha : ℂ)))
  apply (integrableOn_congr_fun (fun r hr => ?_) measurableSet_Ioi).mpr hs
  push_cast
  field_simp [hα]
