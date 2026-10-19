-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.arcsine_integral_x_div_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/ae326aa9-b544-4953-aa88-486868177409

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineIntegral_integral_inv_add_mul_cos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_integral_betaMap_half_half_eq_integral_cos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Interval Topology
open MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
namespace MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
theorem _root_.solution {x : ℝ} (hx : 0 < x) :
    (∫ t, x / (x + t) ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) =
        Real.sqrt (x / (x + 1 / 4)) := by
  rw [integral_betaMap_half_half_eq_integral_cos _ (by fun_prop)]
  have hrewrite :
      (∫ θ in (0 : ℝ)..Real.pi,
        x / (x + (Real.cos θ + 1) / 8)) =
          x * ∫ θ in (0 : ℝ)..Real.pi,
            ((x + 1 / 8) + (1 / 8) * Real.cos θ)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    change x / (x + (Real.cos θ + 1) / 8) =
      x * ((x + 1 / 8) + (1 / 8) * Real.cos θ)⁻¹
    rw [div_eq_mul_inv]
    congr 1
    ring
  rw [hrewrite,
    MetricCodes.Spherical.HigherHierarchy.ArcsineIntegral.integral_inv_add_mul_cos
      (x + 1 / 8) (1 / 8) (by
      norm_num [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      linarith)]
  have hquad : (x + 1 / 8) ^ 2 - (1 / 8 : ℝ) ^ 2 =
      x * (x + 1 / 4) := by ring
  rw [hquad, Real.sqrt_mul hx.le, Real.sqrt_div hx.le]
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hsy : Real.sqrt (x + 1 / 4) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  field_simp [Real.pi_pos.ne', hsx, hsy]
  nlinarith [Real.sq_sqrt hx.le]
end MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
