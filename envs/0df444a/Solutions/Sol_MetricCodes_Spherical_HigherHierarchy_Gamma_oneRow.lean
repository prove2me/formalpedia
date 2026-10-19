-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Gamma_oneRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/7598ac09-7e64-41f2-b544-5eb5ba05909e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Gamma_eq_sub

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {a b : ℝ} (ha : 0 < a) :
    Gamma (oneRowAmbient a) (oneRowStabilizer b) =
      MetricCodes.Gamma a b := by
  have hrad : 0 < a * (1 + a) := by positivity
  have hroot : 0 < Real.sqrt (a * (1 + a)) := Real.sqrt_pos.mpr hrad
  have hlinear : 0 < 1 + 2 * a := by positivity
  have hsquare := Real.sq_sqrt hrad.le
  rw [MetricCodes.Gamma_eq_sub]
  simp [Gamma, lagrangeWeight, lagrangeNumerator, lagrangeDenominator,
    oneRowAmbient, oneRowStabilizer, spectralAtom, quadraticCoordinate,
    Fin.sum_univ_two]
  field_simp [hrad.ne', hroot.ne', hlinear.ne']
  rw [hsquare]
  ring
end MetricCodes.Spherical.HigherHierarchy
