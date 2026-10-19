-- Prove2me | solution 1 for MetricCodes.Hamming.terminalEdgeRayleigh_le_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/d7e04b13-b94e-412b-a9f4-52f043e227a5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminal_edge_sum_le_top

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
    (a b : ℝ) (m n : ℕ)
    (hfit : transverseDegree b n + m ≤ longitudinalDegree a n) :
    terminalEdgeRayleigh a b m n ≤
      topEigenvalue n (transverseDegree b n) (longitudinalDegree a n) := by
  have hkl : transverseDegree b n ≤ longitudinalDegree a n := by omega
  have hm : m ≤ longitudinalDegree a n - transverseDegree b n := by omega
  have hsum :
      (∑ r ∈ Finset.range m,
        MetricCodes.hammingJacobiEntry n (transverseDegree b n)
          (longitudinalDegree a n - (m - r))) =
        ∑ r ∈ Finset.range m,
          MetricCodes.hammingJacobiEntry n (transverseDegree b n)
            (longitudinalDegree a n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m := Finset.mem_range.mp hr
    congr 1
    omega
  unfold terminalEdgeRayleigh
  rw [hsum]
  exact terminal_edge_sum_le_top n
    (transverseDegree b n) (longitudinalDegree a n) m hkl hm
end MetricCodes.Hamming
