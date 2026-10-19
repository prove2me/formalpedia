-- Prove2me | solution 1 for MetricCodes.MRRW.inverseEntropyFactor_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/7253a919-886b-4940-bb57-43881d1d14d8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_inverseVarianceFactor_continuous

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
    Continuous inverseEntropyFactor := by
  unfold inverseEntropyFactor
  exact
    (inverseVarianceFactor_continuous.mul
      Real.continuous_negMulLog).add
      (Real.continuous_negMulLog.comp
        (continuous_id.mul inverseVarianceFactor_continuous))
end MetricCodes.MRRW
