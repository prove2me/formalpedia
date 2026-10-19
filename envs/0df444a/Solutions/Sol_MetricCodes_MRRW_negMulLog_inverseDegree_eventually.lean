-- Prove2me | solution 1 for MetricCodes.MRRW.negMulLog_inverseDegree_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/248c29c6-4221-414a-b1b8-9a08c54b264c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_inverseDegree_eq_sq_mul_factor

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
    (fun r : ℝ => Real.negMulLog (inverseDegree r)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ => r * inverseEntropyFactor r) := by
  have hsmall : ∀ᶠ r : ℝ in 𝓝 0, r ^ 2 < 1 :=
    (continuousAt_id.pow 2).tendsto
      (gt_mem_nhds (by norm_num : (0 : ℝ) ^ 2 < 1))
  filter_upwards [hsmall] with r hr
  rw [inverseDegree_eq_sq_mul_factor hr.le,
    Real.negMulLog_mul]
  unfold inverseEntropyFactor
  ring
end MetricCodes.MRRW
