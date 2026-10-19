-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_quadraticCoordinate_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/d1ff6288-da7a-40a0-b61b-334af76830ee

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
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {u : ℕ → ℝ} {x : ℝ}
    (hu : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => quadraticCoordinate (u n))
      atTop (𝓝 (quadraticCoordinate x)) := by
  unfold quadraticCoordinate
  exact hu.mul ((tendsto_const_nhds (x := (1 : ℝ))).add hu)
end MetricCodes.Spherical.HigherHierarchy
