-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Phi_oneRow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/3c33eea3-ef30-4b45-8096-ec7271cafe24

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
theorem _root_.solution (a b : ℝ) :
    Phi (oneRowAmbient a) (oneRowStabilizer b) =
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
  simp [Phi, oneRowAmbient, oneRowStabilizer, Fin.sum_univ_two]
end MetricCodes.Spherical.HigherHierarchy
