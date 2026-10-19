-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.tendsto_terminalEdgeRayleigh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/14bbe468-7814-4fff-9163-72a192b12717

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_terminal_coefficient
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_tendsto_terminal_coefficient

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped BigOperators Nat Topology InnerProductSpace
open MetricCodes.Spherical.GeneralSpectral
namespace MetricCodes.Spherical.GeneralSpectral
theorem _root_.solution {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    Tendsto (terminalEdgeRayleigh a b m) atTop
      (nhds
        (((m : ℝ) / ((m : ℝ) + 1)) *
          (2 * MetricCodes.Gamma a b))) := by
  have hsum :
      Tendsto
        (fun n : ℕ => ∑ r ∈ Finset.range m,
          SpherePacking.Gegenbauer.jacobiCoefficient
            n (transverseDegree b n)
            (longitudinalDegree a n - (m - r)))
        atTop
        (nhds (∑ _r ∈ Finset.range m, MetricCodes.Gamma a b)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_terminal_coefficient ha hb (m - r)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hquot := (htwo.mul hsum).div_const ((m : ℝ) + 1)
  change
    Tendsto (fun n : ℕ => terminalEdgeRayleigh a b m n) atTop
      (nhds
        (((m : ℝ) / ((m : ℝ) + 1)) *
          (2 * MetricCodes.Gamma a b)))
  simpa [terminalEdgeRayleigh, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using hquot
end MetricCodes.Spherical.GeneralSpectral
