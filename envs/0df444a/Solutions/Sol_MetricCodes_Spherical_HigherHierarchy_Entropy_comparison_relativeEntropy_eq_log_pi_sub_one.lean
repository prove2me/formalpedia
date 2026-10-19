-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_relativeEntropy_eq_log_pi_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/cc7ca240-2456-4dc6-8ef5-33b31aa34a5d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparisonMeasure_rnDeriv_arcsineMeasure
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_relativeEntropy_eq_log_pi_sub_one_of_density

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
theorem _root_.solution
    (hlog : Integrable (fun t : ℝ => Real.log t) comparisonMeasure)
    (hmoment : (∫ t, Real.log t ∂comparisonMeasure) = -2) :
    (InformationTheory.klDiv comparisonMeasure arcsineMeasure).toReal =
      Real.log Real.pi - 1 :=
  comparison_relativeEntropy_eq_log_pi_sub_one_of_density
    comparisonMeasure_rnDeriv_arcsineMeasure hlog hmoment
end MetricCodes.Spherical.HigherHierarchy.Entropy
