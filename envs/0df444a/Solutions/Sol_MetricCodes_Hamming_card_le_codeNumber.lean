-- Prove2me | solution 1 for MetricCodes.Hamming.card_le_codeNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/163709ac-5260-471b-afbe-51fac0ad1c7b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_mem_validCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {n d : ℕ} (C : Finset (BinaryWord n))
    (hC : MetricCodes.IsBinaryCode d C) :
    C.card ≤ codeNumber n d := by
  unfold codeNumber
  exact Finset.le_sup ((mem_validCodes C).2 hC)
end MetricCodes.Hamming
