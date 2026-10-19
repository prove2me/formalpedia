-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.normalizedNu_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/d644af50-02cc-49a5-bea1-b55df26b3d8b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    (a b g u : ℝ)
    (hz : 0 < MetricCodes.Johnson.centeredDegree u) :
    normalizedNu
        (MetricCodes.Johnson.centeredDegree u / 2)
        (MetricCodes.Johnson.centeredWeight a / 2)
        (MetricCodes.Johnson.centeredEta a b g / 2)
        (MetricCodes.Johnson.centeredSigma b g / 2)
        0 =
      nuLimit a b g u := by
  have hrad :
      ((MetricCodes.Johnson.centeredDegree u / 2) ^ 2 -
          (MetricCodes.Johnson.centeredWeight a / 2) ^ 2) *
        ((MetricCodes.Johnson.centeredDegree u / 2) ^ 2 -
          (MetricCodes.Johnson.centeredEta a b g / 2) ^ 2) *
        ((MetricCodes.Johnson.centeredSigma b g / 2) ^ 2 -
          (MetricCodes.Johnson.centeredDegree u / 2) ^ 2) =
      ((1 / 8 : ℝ) ^ 2) *
        ((MetricCodes.Johnson.centeredDegree u ^ 2 -
            MetricCodes.Johnson.centeredWeight a ^ 2) *
          (MetricCodes.Johnson.centeredDegree u ^ 2 -
            MetricCodes.Johnson.centeredEta a b g ^ 2) *
          (MetricCodes.Johnson.centeredSigma b g ^ 2 -
            MetricCodes.Johnson.centeredDegree u ^ 2)) := by
    ring
  have hdenrad :
      (2 * (MetricCodes.Johnson.centeredDegree u / 2)) *
          (2 * (MetricCodes.Johnson.centeredDegree u / 2)) =
        MetricCodes.Johnson.centeredDegree u ^ 2 := by
    ring
  unfold normalizedNu
  simp only [add_zero, sub_zero]
  rw [hrad, hdenrad,
    Real.sqrt_mul (sq_nonneg (1 / 8 : ℝ)),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 8),
    Real.sqrt_sq hz.le]
  unfold nuLimit
  field_simp [hz.ne']
end MetricCodes.Johnson.SpectralAsymptotics
