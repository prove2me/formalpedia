-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Arcsine.betaPDFReal_one_half_eq_mul_half_pi_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/a0ad9617-eb24-45cd-b4d0-982969db5f37

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_beta_half_half_eq_pi
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_beta_one_half_eq_two

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Interval
open MetricCodes.Spherical.HigherHierarchy.Arcsine
namespace MetricCodes.Spherical.HigherHierarchy.Arcsine
theorem _root_.solution (t : ℝ) :
    betaPDFReal 1 (1 / 2 : ℝ) t =
      betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) t *
        (Real.pi / 2 * Real.sqrt t) := by
  by_cases ht : 0 < t ∧ t < 1
  · rw [betaPDFReal, betaPDFReal, if_pos ht, if_pos ht,
      beta_half_half_eq_pi, beta_one_half_eq_two]
    have hsqrt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht.1).ne'
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hpow : t ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt t)⁻¹ := by
      convert Real.rpow_neg ht.1.le (1 / 2 : ℝ) using 1 <;>
        norm_num [Real.sqrt_eq_rpow]
    rw [hpow]
    norm_num
    field_simp
  · simp [betaPDFReal, ht]
end MetricCodes.Spherical.HigherHierarchy.Arcsine
