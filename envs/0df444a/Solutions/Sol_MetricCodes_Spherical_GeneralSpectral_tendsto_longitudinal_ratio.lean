-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.tendsto_longitudinal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/5a055905-a47f-4bea-b9d4-ea32e49a4950

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_SpectralAsymptotics_tendsto_floored_ratio

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
open Filter Topology
open scoped BigOperators Nat Topology InnerProductSpace
open MetricCodes.Spherical.GeneralSpectral
namespace MetricCodes.Spherical.GeneralSpectral
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ =>
      (longitudinalDegree a n : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  exact SpherePacking.SpectralAsymptotics.tendsto_floored_ratio ha
end MetricCodes.Spherical.GeneralSpectral
