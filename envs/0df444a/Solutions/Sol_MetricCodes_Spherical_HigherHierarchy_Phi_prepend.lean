-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Phi_prepend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/23efaf45-2779-4d8e-b20a-e01be95df97e

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
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (u v : ℝ) :
    Phi (prependAmbient u a) (prependStabilizer v b) =
      Phi a b +
        (MetricCodes.sphericalEntropy u - MetricCodes.sphericalEntropy v) := by
  simp [Phi, prependAmbient, prependStabilizer, Fin.sum_univ_succ]
  ring
end MetricCodes.Spherical.HigherHierarchy
