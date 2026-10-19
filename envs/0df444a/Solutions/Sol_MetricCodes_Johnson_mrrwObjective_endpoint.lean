-- Prove2me | solution 1 for MetricCodes.Johnson.mrrwObjective_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/8bcae245-2043-4f41-833a-2f1a235812b9

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_sqrt_one_sub_centeredDegree_sq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwObjective δ (1 - 2 * δ) =
      MetricCodes.Hamming.classicalRate δ := by
  have hlast :
      (1 - 2 * δ) ^ 2 + 2 * δ * (1 - 2 * δ) + 2 * δ =
        (1 : ℝ) := by
    ring
  have hroot :
      Real.sqrt (1 - (1 - 2 * δ) ^ 2) =
        2 * Real.sqrt (δ * (1 - δ)) := by
    simpa [centeredDegree] using
      sqrt_one_sub_centeredDegree_sq hδ hhalf
  calc
    mrrwObjective δ (1 - 2 * δ) =
        mrrwG ((1 - 2 * δ) ^ 2) := by
      unfold mrrwObjective
      rw [hlast, mrrwG_one]
      ring
    _ = MetricCodes.Hamming.classicalRate δ := by
      unfold mrrwG MetricCodes.Hamming.classicalRate
        MetricCodes.Hamming.classicalParameter
      rw [hroot]
      congr 1 ; ring
end MetricCodes.Johnson
