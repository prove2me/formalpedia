-- Prove2me | solution 1 for MetricCodes.Hamming.rateSet_nonempty_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/2343a336-5d5a-4242-9d94-63650767f8f7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_exists_strict_improving_feasible

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    (rateSet δ).Nonempty := by
  obtain ⟨a, b, hfeasible, _⟩ :=
    exists_strict_improving_feasible hδ hδ'
  exact ⟨MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b,
    a, b, hfeasible, rfl⟩
end MetricCodes.Hamming
