-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneCompensatedIntegrationByParts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T10:58:28.885583+00:00
-- url     : https://prove2.me/submissions/397959c6-a3da-4fe3-abc7-65e632c75220

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneHalfLineProductIBP
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h1 : 1 < alpha) (h2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) /
          ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ)
      ∂volume) =
      (Complex.I / (alpha : ℂ)) *
        (∫ r in Set.Ioi (0 : ℝ),
          (Complex.exp (Complex.I * (r : ℂ)) - 1) *
            (((r ^ (- (alpha - 1) - 1) : ℝ)) : ℂ)
          ∂volume) := by
  have hα : (alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one h1))
  have hwhole := Kyprianou.Ch01.stableAlphaAboveOneHalfLineProductIBP
    alpha h1 h2
  have hleft :
      (∫ r in Set.Ioi (0 : ℝ),
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) /
            ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ) ∂volume) =
      (∫ r in Set.Ioi (0 : ℝ),
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) *
          (((r ^ (-(alpha + 1)) : ℝ)) : ℂ) ∂volume) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) /
          (((r ^ (alpha + 1) : ℝ)) : ℂ) =
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) *
          (((r ^ (-(alpha + 1)) : ℝ)) : ℂ)
    rw [Real.rpow_neg hr.le, div_eq_mul_inv]
    norm_cast
  have hpoint (r : ℝ) :
      (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) *
        (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ) =
      (-(Complex.I / (alpha : ℂ))) *
        ((Complex.exp (Complex.I * (r : ℂ)) - 1) *
          (((r ^ (-alpha) : ℝ)) : ℂ)) := by
    push_cast
    field_simp [hα]
  have hright :
      (∫ r in Set.Ioi (0 : ℝ),
        (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ) ∂volume) =
      -(Complex.I / (alpha : ℂ)) *
        (∫ r in Set.Ioi (0 : ℝ),
          (Complex.exp (Complex.I * (r : ℂ)) - 1) *
            (((r ^ (-alpha) : ℝ)) : ℂ) ∂volume) := by
    simp_rw [hpoint]
    exact MeasureTheory.integral_const_mul _ _
  rw [hleft, hwhole, hright]
  have hp : -(alpha - 1) - 1 = -alpha := by ring
  simp only [hp]
  ring
