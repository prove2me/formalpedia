-- Prove2me | solution 1 for MetricCodes.Hamming.terminal_indicator_edge_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/7e5f9bcb-6c7e-40a0-900a-e8a004102b74

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
theorem _root_.solution
    (d m : ℕ) (hm : m ≤ d) (c : ℕ → ℝ) :
    (∑ p ∈ Finset.range d,
      c p * terminalIndicator d m p *
        terminalIndicator d m (p + 1)) =
      ∑ r ∈ Finset.range m, c (d - m + r) := by
  have hsplit : d = (d - m) + m := by omega
  rw [hsplit, Finset.sum_range_add]
  simp only [← hsplit]
  have hfirst :
      (∑ p ∈ Finset.range (d - m),
        c p * terminalIndicator d m p *
          terminalIndicator d m (p + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hp' : p < d - m := Finset.mem_range.mp hp
    simp [terminalIndicator, Nat.not_le.mpr hp']
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro p hp
  have h₁ : d - m ≤ d - m + p := by omega
  have h₂ : d - m ≤ d - m + p + 1 := by omega
  simp only [terminalIndicator, if_pos h₁, if_pos h₂, mul_one]
end MetricCodes.Hamming
