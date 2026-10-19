-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.arcsineMeasure_stieltjesKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/e952ef04-8425-4c0e-9071-d823190a025c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_ArcsineTransform_arcsine_integral_self_div_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {x : ℝ} (hx : 0 ≤ x) :
    (∫ t : ℝ, t / (t + x) ∂Entropy.arcsineMeasure) =
      1 - Real.sqrt (x / (x + 1 / 4)) := by
  simpa [Entropy.arcsineMeasure] using
    ArcsineTransform.arcsine_integral_self_div_add hx
end MetricCodes.Spherical.HigherHierarchy
