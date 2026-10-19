-- Prove2me | solution 1 for MetricCodes.Spherical.HigherChannel.tendsto_flooredCoordinates_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/58fccdc2-1a9d-4901-b6c1-55059b49e948

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
open MetricCodes.Spherical.HigherChannel
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherChannel
theorem _root_.solution {I : Type*}
    (a : I → ℝ) (i : I) (ha : 0 ≤ a i) :
    Tendsto
      (fun n : ℕ => (flooredCoordinates a n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)) := by
  simpa [flooredCoordinates, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
end MetricCodes.Spherical.HigherChannel
