-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.betaPDFReal_half_half_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/b4ee4b39-1307-42bf-a807-4b2a78c7fe9d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_beta_half_half_eq_pi

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
theorem _root_.solution (u : ℝ) (hu₀ : 0 < u) (hu₁ : u < 1) :
    betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u =
      (1 / Real.pi) * (Real.sqrt (u * (1 - u)))⁻¹ := by
  rw [betaPDFReal, if_pos ⟨hu₀, hu₁⟩,
    MetricCodes.Spherical.HigherHierarchy.Arcsine.beta_half_half_eq_pi]
  have hu : 0 ≤ u := hu₀.le
  have hv : 0 ≤ 1 - u := by linarith
  have hpow₁ : u ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt u)⁻¹ := by
    convert Real.rpow_neg hu (1 / 2 : ℝ) using 1 <;>
      norm_num [Real.sqrt_eq_rpow]
  have hpow₂ : (1 - u) ^ ((1 / 2 : ℝ) - 1) =
      (Real.sqrt (1 - u))⁻¹ := by
    convert Real.rpow_neg hv (1 / 2 : ℝ) using 1 <;>
      norm_num [Real.sqrt_eq_rpow]
  rw [hpow₁, hpow₂, Real.sqrt_mul hu, mul_inv_rev]
  ring
end MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
