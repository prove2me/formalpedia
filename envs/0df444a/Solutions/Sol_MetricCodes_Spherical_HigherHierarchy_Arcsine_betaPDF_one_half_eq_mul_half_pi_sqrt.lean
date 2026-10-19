-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Arcsine.betaPDF_one_half_eq_mul_half_pi_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/d11bb861-bf36-4544-8d68-2cf3e8cb4675

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_betaPDFReal_one_half_eq_mul_half_pi_sqrt

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
    betaPDF 1 (1 / 2 : ℝ) t =
      betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ) t *
        ENNReal.ofReal (Real.pi / 2 * Real.sqrt t) := by
  rw [betaPDF, betaPDF, betaPDFReal_one_half_eq_mul_half_pi_sqrt,
    ENNReal.ofReal_mul' (mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num))
      (Real.sqrt_nonneg t))]
end MetricCodes.Spherical.HigherHierarchy.Arcsine
