-- Prove2me | solution 1 for MetricCodes.Hamming.terminal_indicator_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/7cc8a774-6f31-4eb3-b92d-9e7ad955571e

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
theorem _root_.solution (d m : ℕ) (hm : m ≤ d) :
    (∑ p ∈ Finset.range (d + 1), terminalIndicator d m p) =
      (m : ℝ) + 1 := by
  have hsplit : d + 1 = (d - m) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ p ∈ Finset.range (d - m), terminalIndicator d m p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p < d - m := Finset.mem_range.mp hp
    simp [terminalIndicator, Nat.not_le.mpr hp']
  rw [hfirst, zero_add]
  calc
    (∑ p ∈ Finset.range (m + 1),
      terminalIndicator d m (d - m + p)) =
        ∑ _p ∈ Finset.range (m + 1), (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [terminalIndicator]
    _ = (m : ℝ) + 1 := by simp
end MetricCodes.Hamming
