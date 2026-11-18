-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseNearZeroIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:42:06.017729+00:00
-- url     : https://prove2.me/submissions/5d229c5e-949d-4a5b-a215-4d8f83119121

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseKernelMeasurable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneComplexRemainderQuadratic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real Complex
set_option autoImplicit false
/-! The compensated index-one complex Lévy kernel is bounded on an explicit right neighbourhood of zero. -/
theorem solution
    (z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
      (Set.Ioo (0 : ℝ) (1 / (1 + z))) := by
  have hden : 0 < 1 + z := by linarith
  have hdelta : 0 < (1 / (1 + z) : ℝ) := by positivity
  have hconst :
      IntegrableOn (fun _ : ℝ => z ^ 2)
        (Set.Ioo (0 : ℝ) (1 / (1 + z))) := by
    exact integrableOn_const (by rw [Real.volume_Ioo]; finiteness)
  apply hconst.mono'
  · exact
      (Kyprianou.Ch01.stableAlphaOneLogPhaseKernelMeasurable z).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hrpos : 0 < r := hr.1
    have hr0 : r ≠ 0 := ne_of_gt hrpos
    have hmul : (1 + z) * r < 1 := by
      calc
        (1 + z) * r < (1 + z) * (1 / (1 + z)) :=
          mul_lt_mul_of_pos_left hr.2 hden
        _ = 1 := by field_simp
    have hcut : r < 1 := by nlinarith [hmul]
    have hsmall : |z * r| ≤ 1 := by
      rw [abs_of_nonneg (mul_nonneg hz.le hrpos.le)]
      nlinarith [hmul]
    have hTaylor :=
      Kyprianou.Ch01.stableAlphaOneComplexRemainderQuadratic z r hsmall
    have hnorm : ‖((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)‖ = r ^ 2 := by
      simp [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    have heq :
        ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) =
          ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
      Complex.I * (((z * r : ℝ) : ℂ))) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) := by
      simp [hcut]
    rw [heq, norm_div, hnorm]
    calc
      ‖(1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
      Complex.I * (((z * r : ℝ) : ℂ))‖ / r ^ 2 ≤ (z * r) ^ 2 / r ^ 2 :=
        div_le_div_of_nonneg_right hTaylor (sq_nonneg r)
      _ = z ^ 2 := by field_simp
