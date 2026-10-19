-- Prove2me | solution 1 for MetricCodes.Hamming.terminalVector_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/dd9d4e8e-28b2-4002-aeff-ebcd34a38962

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
theorem _root_.solution (k L m : ℕ) :
    terminalVector k L m (Fin.last (L - k)) = 1 := by
  change (if L - k - m ≤ L - k then (1 : ℝ) else 0) = 1
  simp
end MetricCodes.Hamming
