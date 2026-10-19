-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_terminalEdgeRayleigh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/238c418b-ed46-499f-bd38-bab5f2748d91

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_terminal_coefficient

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {a b : ℝ}
    (ha : 0 < a) (ha' : a < 1) (hb : 0 ≤ b) (m : ℕ) :
    Tendsto (terminalEdgeRayleigh a b m) atTop
      (nhds
        (((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b)) := by
  have hsum :
      Tendsto
        (fun n : ℕ => ∑ r ∈ Finset.range m,
          MetricCodes.hammingJacobiEntry n (transverseDegree b n)
            (longitudinalDegree a n - (m - r)))
        atTop
        (nhds (∑ _r ∈ Finset.range m,
          MetricCodes.hammingGamma a b / 2)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_terminal_coefficient ha ha' hb (m - r)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hquot := (htwo.mul hsum).div_const ((m : ℝ) + 1)
  change Tendsto
    (fun n : ℕ => terminalEdgeRayleigh a b m n) atTop
      (nhds (((m : ℝ) / ((m : ℝ) + 1)) * MetricCodes.hammingGamma a b))
  simpa [terminalEdgeRayleigh, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hquot
end MetricCodes.Hamming
