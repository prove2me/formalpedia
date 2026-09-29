-- Prove2me | solution 1 for MeasureTheory.setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bb491c53-efa4-5fc7-9355-1be4c0fe6be1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div

set_option autoImplicit false

open MeasureTheory Set

theorem solution
    (h : ℝ → ℝ → ℂ) (t : ℝ) (ht : 0 < t) :
    ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), h y₁ y₂ =
      ∫ u in Ioi (0 : ℝ), ∫ v in Ioi (0 : ℝ), ((u / (t * v ^ 2) : ℝ) : ℂ) * h (-(u / t)) (u / v) := by

  have inner : ∀ u ∈ Ioi (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ), h (-(u / t)) y₂ =
      ∫ v in Ioi (0 : ℝ), ((u / v ^ 2 : ℝ) : ℂ) * h (-(u / t)) (u / v) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have e1 := integral_comp_mul_left_Ioi (fun y => h (-(u / t)) y) (0 : ℝ) hu0
    rw [mul_zero] at e1
    have e2 := integral_comp_rpow_Ioi (fun y => h (-(u / t)) (u * y)) (p := (-1 : ℝ)) (by norm_num)
    rw [e1] at e2
    have e3 : ∫ x in Ioi (0 : ℝ), h (-(u / t)) x =
        u • ∫ x in Ioi (0 : ℝ), (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • h (-(u / t)) (u * x ^ (-1 : ℝ)) := by
      rw [e2, smul_smul, mul_inv_cancel₀ hu0.ne', one_smul]
    rw [e3, ← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have hv0 : (0 : ℝ) < v := hv
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, smul_smul, Complex.real_smul]
    congr 1
    have : ((-1 : ℝ) - 1) = -(2 : ℝ) := by norm_num
    rw [this, abs_neg, abs_one, one_mul, Real.rpow_neg hv0.le, Real.rpow_two]
    push_cast
    ring

  have o1 := integral_comp_neg_Ioi (0 : ℝ) (fun y₁ => ∫ y₂ in Ioi (0 : ℝ), h y₁ y₂)
  rw [neg_zero, integral_Iic_eq_integral_Iio] at o1
  have o2 := integral_comp_mul_left_Ioi (fun x => ∫ y₂ in Ioi (0 : ℝ), h (-x) y₂) (0 : ℝ) (inv_pos.2 ht)
  rw [mul_zero, inv_inv] at o2
  have o3 : ∫ x in Ioi (0 : ℝ), (∫ y₂ in Ioi (0 : ℝ), h (-x) y₂) =
      t⁻¹ • ∫ u in Ioi (0 : ℝ), (∫ y₂ in Ioi (0 : ℝ), h (-(t⁻¹ * u)) y₂) := by
    rw [o2, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  rw [← o1, o3, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [show t⁻¹ * u = u / t by ring, inner u hu, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  rw [Complex.real_smul, ← mul_assoc]
  congr 1
  push_cast
  ring

end S_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div
end P2MW
export P2MW.S_MeasureTheory_setIntegral_Iio_setIntegral_Ioi_eq_setIntegral_setIntegral_mul_comp_neg_div_div (solution)
