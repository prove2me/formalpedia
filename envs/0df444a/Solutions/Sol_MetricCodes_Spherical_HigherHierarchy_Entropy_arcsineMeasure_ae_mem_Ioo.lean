-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.arcsineMeasure_ae_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/e626d6ff-8c06-444c-9e05-f4c0a76dd559

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_betaMeasure_ae_mem_Ioo

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Entropy
namespace MetricCodes.Spherical.HigherHierarchy.Entropy
theorem _root_.solution :
    ∀ᵐ t ∂arcsineMeasure, t ∈ Set.Ioo (0 : ℝ) endpoint := by
  unfold arcsineMeasure endpoint
  change ∀ᵐ t ∂(betaMeasure (1 / 2) (1 / 2)).map (fun t : ℝ => t / 4),
    0 < t ∧ t < (1 / 4 : ℝ)
  rw [ae_map_iff (by fun_prop) measurableSet_Ioo]
  filter_upwards [betaMeasure_ae_mem_Ioo] with t ht
  constructor <;> nlinarith [ht.1, ht.2]
end MetricCodes.Spherical.HigherHierarchy.Entropy
