-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.terminal_indicator_diagonal_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/529387ca-e555-4c2e-b69d-fb99db2657a5

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
    (d m : ℕ) (hm : m ≤ d) (b : ℕ → ℝ) :
    (∑ i ∈ Finset.range (d + 1),
      b i * MetricCodes.Hamming.terminalIndicator d m i ^ 2) =
      ∑ r ∈ Finset.range (m + 1), b (d - m + r) := by
  have hsplit : d + 1 = (d - m) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ i ∈ Finset.range (d - m),
        b i * MetricCodes.Hamming.terminalIndicator d m i ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < d - m := Finset.mem_range.mp hi
    simp [MetricCodes.Hamming.terminalIndicator, Nat.not_le.mpr hi']
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro r hr
  have hmem : d - m ≤ d - m + r := by omega
  simp [MetricCodes.Hamming.terminalIndicator, hmem]
end MetricCodes.Johnson.SpectralAsymptotics
