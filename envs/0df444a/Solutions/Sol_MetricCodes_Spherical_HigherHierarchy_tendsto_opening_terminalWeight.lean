-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.tendsto_opening_terminalWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/434cadee-9776-4b6f-9d49-45e041123850

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_lagrangeWeight_opening_scaledDerivative

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
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hzero : a (Fin.last r) = 0) (η : ℝ) :
    Tendsto
      (fun t : ℝ =>
        lagrangeWeight (openingAmbient a (η * t) (t ^ 2)) b (Fin.last r))
      (𝓝[>] 0)
      (nhds (lagrangeWeight a b (Fin.last r))) := by
  obtain ⟨_, d, hd, _⟩ :=
    lagrangeWeight_opening_scaledDerivative h hzero η (Fin.last r)
  have ht := hd.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa [openingAmbient_zero hzero] using ht
end MetricCodes.Spherical.HigherHierarchy
