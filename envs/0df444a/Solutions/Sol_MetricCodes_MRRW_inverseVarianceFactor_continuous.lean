-- Prove2me | solution 1 for MetricCodes.MRRW.inverseVarianceFactor_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/72044d7d-7996-40e9-ab29-e5867e9fa9de

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution :
    Continuous inverseVarianceFactor := by
  unfold inverseVarianceFactor
  apply Continuous.inv₀
  · fun_prop
  · intro r
    have hroot : 0 ≤ Real.sqrt (1 - r ^ 2) :=
      Real.sqrt_nonneg _
    positivity
end MetricCodes.MRRW
