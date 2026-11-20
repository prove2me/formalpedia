-- Prove2me | solution 1 for Kyprianou.Ch01.stableTwoSidedTrigSkewFactor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:42:22.161781+00:00
-- url     : https://prove2.me/submissions/c19a7a98-6d9a-4dff-b74e-a2167c4a8aa4

import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open Complex Real Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (cpos cneg theta : ℝ)
    (hsum : cpos + cneg ≠ 0)
    (hcos : Real.cos theta ≠ 0) :
    (cpos : ℂ) * ((Real.cos theta : ℝ) -
       Complex.I * (Real.sin theta : ℂ)) +
    (cneg : ℂ) * ((Real.cos theta : ℝ) +
       Complex.I * (Real.sin theta : ℂ)) =
      (((cpos + cneg) * Real.cos theta : ℝ) : ℂ) *
        (1 - Complex.I *
          (((cpos - cneg) / (cpos + cneg) *
              Real.tan theta : ℝ) : ℂ)) := by
  rw [Real.tan_eq_sin_div_cos]
  have hs : ((cpos + cneg : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsum
  have hc : ((Real.cos theta : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcos
  push_cast
  have hcn : Complex.cos (theta : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_cos] using hc
  have hss : (cpos : ℂ) + (cneg : ℂ) ≠ 0 := by
    simpa only [← Complex.ofReal_add] using hs
  have hdenom :
      (cpos : ℂ) * Complex.cos (theta : ℂ) +
      Complex.cos (theta : ℂ) * (cneg : ℂ) ≠ 0 := by
    have heq :
        (cpos : ℂ) * Complex.cos (theta : ℂ) +
        Complex.cos (theta : ℂ) * (cneg : ℂ) =
          ((cpos : ℂ) + (cneg : ℂ)) * Complex.cos (theta : ℂ) := by ring
    rw [heq]
    exact mul_ne_zero hss hcn
  field_simp [hs, hc, hss, hcn, hdenom]
  ring
