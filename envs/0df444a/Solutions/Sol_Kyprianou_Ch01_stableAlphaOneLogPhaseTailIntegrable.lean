-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseTailIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:42:13.116553+00:00
-- url     : https://prove2.me/submissions/c1b439f8-7562-44ed-9ad2-1a31157956d5

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseKernelMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real Complex
set_option autoImplicit false
/-! The fully compensated complex stable kernel has an integrable r^{-2} tail. -/
theorem solution
    (z : ℝ) :
    IntegrableOn (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
      (Set.Ioi (1 : ℝ)) := by
  have hpow : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ))
      (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 (by norm_num)
  have htwo : IntegrableOn (fun r : ℝ => 2 * r ^ (-2 : ℝ))
      (Ioi (1 : ℝ)) := hpow.const_mul 2
  apply htwo.mono'
  · exact
      (Kyprianou.Ch01.stableAlphaOneLogPhaseKernelMeasurable z).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrpos : 0 < r := (by norm_num : (0 : ℝ) < 1).trans hr
    have hcut : ¬r < 1 := not_lt.mpr hr.le
    have hexp : ‖Complex.exp (Complex.I * (((z * r : ℝ) : ℂ)))‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re]
    have hbound :
        ‖(1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ)))‖ ≤ 2 := calc
      _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (Complex.I * (((z * r : ℝ) : ℂ)))‖ :=
        norm_sub_le _ _
      _ = 2 := by
        simp [Complex.norm_exp, Complex.mul_re]
        norm_num
    have hnorm : ‖((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)‖ = r ^ 2 := by
      simp [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    have hpoweq : r ^ (-2 : ℝ) = (r ^ 2)⁻¹ := by
      rw [Real.rpow_neg hrpos.le]
      exact congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast r 2)
    have heq : ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) =
      ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ)))) / ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) := by
      simp [hcut]
    rw [heq, norm_div, hnorm, hpoweq]
    simpa [div_eq_mul_inv] using
      (div_le_div_of_nonneg_right hbound (sq_nonneg r))
