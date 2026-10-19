-- Prove2me | solution 1 for MetricCodes.MRRW.spectralLimit_interior_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/1fa8a0b5-7531-4263-8c71-750dff9ea821

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
theorem _root_.solution (a u e : ℝ) :
    MetricCodes.Johnson.spectralLimit
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u =
      let z := MetricCodes.Johnson.centeredDegree u
      let m := MetricCodes.Johnson.centeredWeight (interiorWeight a u e)
      let t := 1 - 2 * e
      (m * (t ^ 2 - z ^ 2)) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
        ((z ^ 2 - (m * t) ^ 2) * (t ^ 2 - z ^ 2)) /
          (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2)) := by
  dsimp [MetricCodes.Johnson.spectralLimit,
    MetricCodes.Johnson.centeredDegree, MetricCodes.Johnson.centeredWeight,
    MetricCodes.Johnson.centeredSigma, MetricCodes.Johnson.centeredEta,
    interiorSupport, interiorComplement]
  ring
end MetricCodes.MRRW
