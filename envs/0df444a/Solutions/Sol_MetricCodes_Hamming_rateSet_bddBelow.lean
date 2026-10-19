-- Prove2me | solution 1 for MetricCodes.Hamming.rateSet_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/ab99266d-2c08-474a-9c49-93b66dfb4a01

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_binaryEntropy_nonneg
import Theorems.Thm_MetricCodes_Hamming_binaryEntropy_le_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution (δ : ℝ) : BddBelow (rateSet δ) := by
  refine ⟨-1, ?_⟩
  rintro r ⟨a, b, hfeasible, rfl⟩
  obtain ⟨hb, hba, ha, hgamma⟩ := hfeasible
  have ha0 : 0 ≤ a := (lt_of_le_of_lt hb hba).le
  have ha1 : a ≤ 1 := by linarith
  have hapos := MetricCodes.binaryEntropy_nonneg ha0 ha1
  have hble := binaryEntropy_le_one b
  linarith
end MetricCodes.Hamming
