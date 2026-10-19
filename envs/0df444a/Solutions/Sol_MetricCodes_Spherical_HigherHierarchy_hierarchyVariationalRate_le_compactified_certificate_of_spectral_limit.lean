-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_le_compactified_certificate_of_spectral_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/94b8bac7-b01c-4798-81f2-ef29b4d7bef8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_nextLevel_compactified_certificate_lt_of_spectral_limit

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s c : ℝ}
    (hc : 0 < c) (hc' : c < 1)
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (hscaled : s < 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hGamma : Tendsto
      (fun u : ℝ => Gamma (prependAmbient u a)
        (prependStabilizer (scaleCoordinate (c ^ 2) u) b))
      atTop (𝓝 (((1 - c ^ 2) / 2) + c ^ 2 * Gamma a b))) :
    hierarchyVariationalRate s ≤ Phi a b - Real.logb 2 c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨A, B, hAB, hgap, hPhi⟩ :=
    exists_nextLevel_compactified_certificate_lt_of_spectral_limit
      (R := Phi a b - Real.logb 2 c + ε)
      hc hc' a b h hscaled (by linarith) hGamma
  exact (hierarchyVariationalRate_le_of_feasible hAB hgap).trans hPhi.le
end MetricCodes.Spherical.HigherHierarchy
