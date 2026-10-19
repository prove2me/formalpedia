-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.packingObjective_le_limitingPackingExponent_of_logMoment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/3f4b610e-78ca-45cd-8071-e37c02639525

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Entropy_packingExponent_deficit_eq_relativeEntropy_of_logMoment

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
    {Γ Φ : ℝ} {K : ℝ → ℝ}
    (hlogMoment : (∫ t, Real.log t ∂comparisonMeasure) = -2)
    (hphase : Integrable K comparisonMeasure)
    (htilt : Integrable (fun t => Real.exp (-K t)) arcsineMeasure)
    (hnormalizer : phaseNormalizer K = 1 - 2 * Γ)
    (hphaseMoment : (∫ t, K t ∂comparisonMeasure) =
      2 * Real.log 2 * Φ) :
    packingObjective Γ Φ ≤ limitingPackingExponent := by
  have hgap := packingExponent_deficit_eq_relativeEntropy_of_logMoment
    hlogMoment hphase htilt hnormalizer hphaseMoment
  have hden : 0 < 2 * Real.log (2 : ℝ) := by
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hnonneg :
      0 ≤ (InformationTheory.klDiv comparisonMeasure (phaseTilt K)).toReal /
        (2 * Real.log 2) :=
    div_nonneg ENNReal.toReal_nonneg hden.le
  linarith
end MetricCodes.Spherical.HigherHierarchy.Entropy
