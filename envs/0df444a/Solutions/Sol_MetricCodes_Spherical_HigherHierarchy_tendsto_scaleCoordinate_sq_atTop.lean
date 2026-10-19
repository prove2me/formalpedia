-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_scaleCoordinate_sq_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/9bbeb4bb-acce-4492-a939-9e778e2a594d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_scaleCoordinate_sq_div_atTop

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
theorem _root_.solution {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => scaleCoordinate (c ^ 2) u) atTop atTop := by
  have hratio := tendsto_scaleCoordinate_sq_div_atTop hc
  have hevent :
      ∀ᶠ u : ℝ in atTop, c / 2 < scaleCoordinate (c ^ 2) u / u :=
    hratio.eventually (Ioi_mem_nhds (by linarith))
  have hle :
      (fun u : ℝ => (c / 2) * u) ≤ᶠ[atTop]
        (fun u : ℝ => scaleCoordinate (c ^ 2) u) := by
    filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with u hu hupos
    have hmul := (lt_div_iff₀ hupos).mp hu
    exact hmul.le
  exact tendsto_atTop_mono' atTop hle
    (tendsto_id.const_mul_atTop (by linarith))
end MetricCodes.Spherical.HigherHierarchy
