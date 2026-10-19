-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.comparisonMeasure_ae_positive_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/87bbc449-b1e1-4206-adb8-a0505a09f483

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparisonMeasure_ae_mem_Ioo

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
theorem _root_.solution :
    ∀ᵐ t ∂Entropy.comparisonMeasure, 0 < t ∧ t ≤ 1 := by
  filter_upwards [Entropy.comparisonMeasure_ae_mem_Ioo] with t ht
  constructor
  · exact ht.1
  · have hendpoint : Entropy.endpoint = (1 / 4 : ℝ) := rfl
    rw [hendpoint] at ht
    linarith [ht.2]
end MetricCodes.Spherical.HigherHierarchy
