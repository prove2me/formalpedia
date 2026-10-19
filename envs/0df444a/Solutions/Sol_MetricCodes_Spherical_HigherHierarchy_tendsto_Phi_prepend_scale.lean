-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_Phi_prepend_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/2bb1f50e-1703-4fc9-b50d-62b35d30600c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_prepend
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_entropy_prepend_scale

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
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ =>
      Phi (prependAmbient u a)
        (prependStabilizer (scaleCoordinate (c ^ 2) u) b))
      atTop (𝓝 (Phi a b - Real.logb 2 c)) := by
  simpa only [Phi_prepend, sub_eq_add_neg] using
    (tendsto_const_nhds (x := Phi a b)).add
      (tendsto_entropy_prepend_scale hc)
end MetricCodes.Spherical.HigherHierarchy
