-- Prove2me | solution 1 for MetricCodes.Hamming.longitudinalDegree_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/56613532-ed23-4447-b48e-7f212c1af542

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
theorem _root_.solution {a : ℝ}
    (ha : a ≤ (1 : ℝ) / 2) (n : ℕ) :
    longitudinalDegree a n ≤ n / 2 := by
  unfold longitudinalDegree
  calc
    Nat.floor (a * (n : ℝ)) ≤ Nat.floor ((n : ℝ) / 2) := by
      apply Nat.floor_mono
      have h := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n)
      linarith
    _ = n / 2 := by
      simpa using (Nat.floor_div_eq_div (K := ℝ) n 2)
end MetricCodes.Hamming
