-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.arcsine_stieltjes_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/a457a3ee-edbc-4a8f-88a2-759678322229

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_betaMap_half_half_ae_pos

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
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun t : ℝ => x / (x + t))
      ((betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
        (fun t : ℝ => t / 4)) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((by fun_prop : Measurable (fun t : ℝ => x / (x + t))).aestronglyMeasurable)
  filter_upwards [betaMap_half_half_ae_pos] with t ht
  have hden : 0 < x + t := by linarith
  have hnonneg : 0 ≤ x / (x + t) := div_nonneg hx hden.le
  simpa [norm_div, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_pos hden] using
    ((div_le_one hden).2 (by linarith : x ≤ x + t))
end MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
