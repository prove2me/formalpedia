-- Prove2me | solution 1 for MetricCodes.MRRW.hasDerivAt_mul_continuous_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/ef550b96-b85f-4e21-91e4-0be78580feef

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
theorem _root_.solution
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (hgzero : g 0 = 0) :
    HasDerivAt (fun r : ℝ => r * g r) 0 0 := by
  apply (hasDerivAt_iff_tendsto_slope_zero).2
  have htend : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa [hgzero] using
      hg.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hquotient :
      Tendsto (fun r : ℝ => r⁻¹ * (r * g r))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine (tendsto_congr' ?_).2 htend
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrzero : r ≠ 0 := by simpa using hr
    field_simp [hrzero]
  simpa [smul_eq_mul] using hquotient
end MetricCodes.MRRW
