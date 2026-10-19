-- Prove2me | solution 1 for MetricCodes.MRRW.hasDerivAt_negMulLog_inverseDegree_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/f8a3e7be-aed5-483f-a16c-a3ca397ef148

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_hasDerivAt_mul_continuous_zero
import Theorems.Thm_MetricCodes_MRRW_inverseEntropyFactor_continuous
import Theorems.Thm_MetricCodes_MRRW_negMulLog_inverseDegree_eventually

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
    HasDerivAt (fun r : ℝ => Real.negMulLog (inverseDegree r)) 0 0 := by
  exact
    (hasDerivAt_mul_continuous_zero inverseEntropyFactor
      inverseEntropyFactor_continuous.continuousAt
      inverseEntropyFactor_zero).congr_of_eventuallyEq
      negMulLog_inverseDegree_eventually
end MetricCodes.MRRW
