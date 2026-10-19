-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparison_logLikelihood_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/34f47e67-0785-4c75-a498-472f0af54b31

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparisonMeasure_rnDeriv_arcsineMeasure
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_comparison_logLikelihood_integrable_of_density

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
    (hlog : Integrable (fun t : ℝ => Real.log t) comparisonMeasure) :
    Integrable (llr comparisonMeasure arcsineMeasure) comparisonMeasure :=
  comparison_logLikelihood_integrable_of_density
    comparisonMeasure_rnDeriv_arcsineMeasure hlog
end MetricCodes.Spherical.HigherHierarchy.Entropy
