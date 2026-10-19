-- Prove2me | solution 1 for MetricCodes.MRRW.eventually_interiorSpectralMargin_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/bceae22f-a625-43d9-85f2-e1ac232e0901

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_interiorSpectralMargin_zero
import Theorems.Thm_MetricCodes_MRRW_hasDerivAt_interiorSpectralMargin
import Theorems.Thm_MetricCodes_MRRW_interiorSpectralMargin_derivative_pos

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
    {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < interiorSpectralMargin δ a u e := by
  have hderiv :=
    hasDerivAt_interiorSpectralMargin hu hua ha hboundary
  have hpositive := interiorSpectralMargin_derivative_pos hu hua ha
  have hslope := hderiv.tendsto_slope_zero_right
  have heventual := hslope.eventually (lt_mem_nhds hpositive)
  filter_upwards [heventual, self_mem_nhdsWithin]
    with e he (hepos : 0 < e)
  have hzero := interiorSpectralMargin_zero hboundary
  have hslopepos : 0 < e⁻¹ * interiorSpectralMargin δ a u e := by
    simpa [hzero, smul_eq_mul] using he
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hepos)).mp hslopepos
end MetricCodes.MRRW
