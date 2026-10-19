-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_interlacing_prepend_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/5da98214-a0f1-4895-a16c-b4e57d0f9c7d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_interlacing_prepend
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_scaleCoordinate_sq_atTop
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_scaleCoordinate_sq_lt_self

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
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {c : ℝ} (hc : 0 < c) (hc' : c < 1) :
    ∀ᶠ u : ℝ in atTop,
      Interlacing (prependAmbient u a)
        (prependStabilizer (scaleCoordinate (c ^ 2) u) b) := by
  have hlarge := (tendsto_scaleCoordinate_sq_atTop hc).eventually
    (eventually_gt_atTop (a 0))
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℝ)] with u hu hupos
  exact interlacing_prepend h (scaleCoordinate_sq_lt_self hc hc' hupos) hu
end MetricCodes.Spherical.HigherHierarchy
