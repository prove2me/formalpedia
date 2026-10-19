-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.lagrangeNumerator_append_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/6f5d694c-3bff-4adc-b01c-9ecff471fb07

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
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ε : ℝ) (i : Fin (r + 1)) :
    lagrangeNumerator (appendAmbient a) (appendStabilizer b ε) i.castSucc =
      lagrangeNumerator a b i *
        (quadraticCoordinate (a i) - quadraticCoordinate ε) := by
  unfold lagrangeNumerator appendAmbient appendStabilizer
  rw [Fin.prod_univ_castSucc]
  simp
end MetricCodes.Spherical.HigherHierarchy
