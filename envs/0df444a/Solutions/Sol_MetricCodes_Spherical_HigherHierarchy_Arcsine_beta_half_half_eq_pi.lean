-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Arcsine.beta_half_half_eq_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/e3a6af26-f367-4259-b4dc-8532bf722970

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
theorem _root_.solution :
    beta (1 / 2 : ℝ) (1 / 2 : ℝ) = Real.pi := by
  rw [beta, Real.Gamma_one_half_eq]
  norm_num [Real.Gamma_one]
  simpa [pow_two] using Real.sq_sqrt Real.pi_pos.le
end MetricCodes.Spherical.HigherHierarchy.Arcsine
