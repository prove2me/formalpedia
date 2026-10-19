-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.ArcsineTransform.betaMap_half_half_ae_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/956d54ee-f8f6-40c0-8540-6a2be16026af

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Interval Topology
open MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
namespace MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
theorem _root_.solution :
    ∀ᵐ t ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4), 0 < t := by
  rw [ae_map_iff (by fun_prop) measurableSet_Ioi]
  change ∀ᵐ t ∂volume.withDensity
    (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)), 0 < t / 4
  have hmeas : Measurable (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    (measurable_betaPDFReal _ _).ennreal_ofReal
  rw [ae_withDensity_iff hmeas]
  filter_upwards [] with t ht
  by_contra hnot
  have htzero : t ≤ 0 := by
    have : t / 4 ≤ 0 := le_of_not_gt hnot
    linarith
  apply ht
  simp [betaPDF, betaPDFReal, not_lt_of_ge htzero]
end MetricCodes.Spherical.HigherHierarchy.ArcsineTransform
