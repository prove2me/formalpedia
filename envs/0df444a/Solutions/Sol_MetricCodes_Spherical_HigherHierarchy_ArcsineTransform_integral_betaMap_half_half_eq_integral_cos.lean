-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.integral_betaMap_half_half_eq_integral_cos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/33da728f-0262-422d-af14-e90bbbe99024

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_integral_beta_half_half_eq_integral_measureT

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
theorem _root_.solution
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) =
        (1 / Real.pi) *
          ∫ θ in (0 : ℝ)..Real.pi, f ((Real.cos θ + 1) / 8) := by
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_beta_half_half_eq_integral_measureT,
    Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  ring_nf
end MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
