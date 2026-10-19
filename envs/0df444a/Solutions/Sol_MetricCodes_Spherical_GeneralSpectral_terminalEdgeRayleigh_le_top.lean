-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.terminalEdgeRayleigh_le_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/e2388f4f-6f1a-46b3-9ee3-0c2d11589242

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminal_edge_sum_le_top
import Theorems.Thm_SpherePacking_SpectralAsymptotics_terminal_edge_sum_le_top

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
theorem _root_.solution
    (a b : ℝ) (m n : ℕ)
    (hfit : transverseDegree b n + m ≤ longitudinalDegree a n) :
    terminalEdgeRayleigh a b m n ≤
      SpherePacking.Jacobi.topEigenvalue
        n (transverseDegree b n) (longitudinalDegree a n) := by
  have hkl : transverseDegree b n ≤ longitudinalDegree a n := by omega
  have hm : m ≤ longitudinalDegree a n - transverseDegree b n := by omega
  have hsum :
      (∑ r ∈ Finset.range m,
        SpherePacking.Gegenbauer.jacobiCoefficient
          n (transverseDegree b n)
          (longitudinalDegree a n - (m - r))) =
        ∑ r ∈ Finset.range m,
          SpherePacking.Gegenbauer.jacobiCoefficient
            n (transverseDegree b n)
            (longitudinalDegree a n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m := Finset.mem_range.mp hr
    congr 1
    omega
  unfold terminalEdgeRayleigh
  rw [hsum]
  exact SpherePacking.SpectralAsymptotics.terminal_edge_sum_le_top
    n (transverseDegree b n) (longitudinalDegree a n) m hkl hm
end MetricCodes.Spherical.GeneralSpectral
