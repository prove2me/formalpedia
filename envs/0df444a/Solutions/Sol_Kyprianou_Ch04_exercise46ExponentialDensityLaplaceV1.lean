-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46ExponentialDensityLaplaceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:58:29.281658+00:00
-- url     : https://prove2.me/submissions/8723c1c6-2e50-4742-b3d6-9a4a676aed13

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positiveLIntegral_exp_neg_mul_Ioi
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (a b s : Real) (ha : 0 ≤ a) (hb : 0 < b) (hs : 0 ≤ s) :
    (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-s * x))
      ∂(((volume : Measure Real).restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (a * Real.exp (-b*x))))) =
      ENNReal.ofReal (a / (b+s)) := by
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have he : (fun x : Real => ENNReal.ofReal (a * Real.exp (-b*x)) *
      ENNReal.ofReal (Real.exp (-s*x))) =
      (fun x => ENNReal.ofReal a * ENNReal.ofReal (Real.exp (-(b+s)*x))) := by
    funext x
    rw [← ENNReal.ofReal_mul (mul_nonneg ha (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul ha]
    congr 1
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  change (∫⁻ x in Ioi (0 : Real), ENNReal.ofReal (a * Real.exp (-b*x)) *
    ENNReal.ofReal (Real.exp (-s*x))) = _
  rw [show (fun x : Real => ENNReal.ofReal (a * Real.exp (-b*x)) *
    ENNReal.ofReal (Real.exp (-s*x))) = _ from he,
    lintegral_const_mul _ (by fun_prop),
    AvramDividend.Classical.positiveLIntegral_exp_neg_mul_Ioi (b+s) 0 (by linarith),
    ← ENNReal.ofReal_mul ha]
  simp [div_eq_mul_inv]
