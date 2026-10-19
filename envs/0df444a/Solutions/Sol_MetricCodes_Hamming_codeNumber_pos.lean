-- Prove2me | solution 1 for MetricCodes.Hamming.codeNumber_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/369f6fda-b3f1-4b19-a9ed-4939f3afb760

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_card_le_codeNumber

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution (n d : ℕ) : 0 < codeNumber n d := by
  classical
  let x : BinaryWord n := fun _ => false
  have hcode : MetricCodes.IsBinaryCode d ({x} : Finset (BinaryWord n)) := by
    intro u hu v hv huv
    have hu' : u = x := Finset.mem_singleton.mp hu
    have hv' : v = x := Finset.mem_singleton.mp hv
    exact False.elim (huv (hu'.trans hv'.symm))
  have hcard : 1 ≤ codeNumber n d := by
    simpa using card_le_codeNumber ({x} : Finset (BinaryWord n)) hcode
  omega
end MetricCodes.Hamming
