-- Prove2me | solution 1 for MetricCodes.Hamming.ceil_distance_le_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/cff8d81e-2056-4f51-b292-ea6becb2e34f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {δ : ℝ} (hδ : δ ≤ 1) (n : ℕ) :
    Nat.ceil (δ * (n : ℝ)) ≤ n := by
  apply Nat.ceil_le.mpr
  calc
    δ * (n : ℝ) ≤ 1 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n)
    _ = (n : ℝ) := one_mul _
end MetricCodes.Hamming
