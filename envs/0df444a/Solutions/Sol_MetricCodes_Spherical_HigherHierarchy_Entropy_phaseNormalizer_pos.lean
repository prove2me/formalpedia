-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.phaseNormalizer_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/c612fdc9-a28d-44a3-84aa-b8e249acf121

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
theorem _root_.solution {K : ℝ → ℝ}
    (hK : Integrable (fun t => Real.exp (-K t)) arcsineMeasure) :
    0 < phaseNormalizer K := by
  exact integral_exp_pos hK
end MetricCodes.Spherical.HigherHierarchy.Entropy
