-- Prove2me | solution 1 for MetricCodes.Hamming.mem_validCodes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/2799a7ef-3099-4dd3-af70-f7bfdfd97e40

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
theorem _root_.solution {n d : ℕ} (C : Finset (BinaryWord n)) :
    C ∈ validCodes n d ↔ MetricCodes.IsBinaryCode d C := by
  classical
  simp [validCodes]
end MetricCodes.Hamming
