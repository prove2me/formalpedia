-- Prove2me | solution 1 for MetricCodes.Hamming.terminalVector_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/6e9da455-3de6-4b52-8528-dcd283a0050a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminalVector_last

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
    terminalVector k L m ≠ 0 := by
  intro h
  have hx := congrArg
    (fun x : Space k L => x (Fin.last (L - k))) h
  simp [terminalVector_last] at hx
end MetricCodes.Hamming
