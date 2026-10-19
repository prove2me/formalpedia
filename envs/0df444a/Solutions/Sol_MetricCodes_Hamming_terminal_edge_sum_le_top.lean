-- Prove2me | solution 1 for MetricCodes.Hamming.terminal_edge_sum_le_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/ac7e74f7-e586-4c28-ad31-7f9519ab630e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminalVector_ne_zero
import Theorems.Thm_MetricCodes_Hamming_terminalVector_rayleigh

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
    (n k L m : ℕ) (hkl : k ≤ L) (hm : m ≤ L - k) :
    (2 * ∑ r ∈ Finset.range m,
      MetricCodes.hammingJacobiEntry n k (L - m + r)) /
        ((m : ℝ) + 1) ≤ topEigenvalue n k L := by
  rw [← terminalVector_rayleigh n k L m hkl hm]
  exact rayleigh_le_top n k L
    (terminalVector k L m) (terminalVector_ne_zero k L m)
end MetricCodes.Hamming
