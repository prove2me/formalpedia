-- Prove2me | solution 1 for MetricCodes.Hamming.variationalRate_le_of_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/e0eafb00-bc6a-4def-b758-8945a79aa801

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_rateSet_bddBelow

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {δ a b : ℝ}
    (h : Feasible δ a b) :
    variationalRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  exact csInf_le (rateSet_bddBelow δ) ⟨a, b, h, rfl⟩
end MetricCodes.Hamming
