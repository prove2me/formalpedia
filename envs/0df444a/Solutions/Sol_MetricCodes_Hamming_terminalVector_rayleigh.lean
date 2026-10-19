-- Prove2me | solution 1 for MetricCodes.Hamming.terminalVector_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/d1480b34-84cd-41ea-9582-d05a9f4f4770

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminalVector_norm_sq
import Theorems.Thm_MetricCodes_Hamming_terminalVector_inner

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
    rayleigh n k L (terminalVector k L m) =
      (2 * ∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n k (L - m + r)) /
          ((m : ℝ) + 1) := by
  rw [rayleigh_eq_inner,
    terminalVector_inner n k L m hkl hm,
    terminalVector_norm_sq k L m hm]
end MetricCodes.Hamming
