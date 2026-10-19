-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.oneRowInterlacing_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/9956a3bf-fdcd-41d3-89ef-ffbbb61ec294

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
theorem _root_.solution {a b : ℝ} :
    Interlacing (oneRowAmbient a) (oneRowStabilizer b) ↔
      0 < b ∧ b < a := by
  simp [Interlacing, oneRowAmbient, oneRowStabilizer, Fin.forall_fin_one,
    and_comm]
end MetricCodes.Spherical.HigherHierarchy
