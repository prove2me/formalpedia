-- Prove2me | solution 1 for MetricCodes.MRRW.eventually_interior_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/637cc14d-14ca-41e5-adc0-50119fb35671

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_interior_boundary_weight_gt_distance
import Theorems.Thm_MetricCodes_MRRW_eventually_interior_parameters
import Theorems.Thm_MetricCodes_MRRW_eventually_interiorSpectralMargin_pos

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
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.Feasible δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u := by
  have hweight := interior_boundary_weight_gt_distance
    hδ hu hua ha hboundary
  have hparameters := eventually_interior_parameters
    hδ hδ' hweight hu hua ha
  have hspectral := eventually_interiorSpectralMargin_pos
    hu hua ha hboundary
  filter_upwards [hparameters, hspectral] with e he hs
  refine ⟨he, ?_⟩
  change
    MetricCodes.Johnson.asymptoticThreshold δ (interiorWeight a u e) <
      MetricCodes.Johnson.spectralLimit
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u
  exact sub_pos.mp hs
end MetricCodes.MRRW
