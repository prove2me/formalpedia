-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_compactified_levelRate_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/cce25cf2-3764-4305-aa14-91dc5af64160

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_levelRate_minimizing_sequence
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_minimizing_sequence_bddAbove
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactified_certificate_residual_threshold_le
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_fixedLevelForwardCompactifiedResidualLimit

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
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ (j : ℕ) (c : ℝ)
      (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ),
      0 < c ∧ c ≤ 1 ∧ Interlacing a b ∧
      ((c = 1 ∧ j ≤ r) ∨ (c < 1 ∧ j + 1 ≤ r)) ∧
      s ≤ 1 - c ^ 2 * (1 - 2 * Gamma a b) ∧
      levelRate r s = Phi a b - Real.logb 2 c := by
  obtain ⟨a, b, hfeasible, hanti, hlimit⟩ :=
    exists_levelRate_minimizing_sequence
      (levelRateSet_nonempty_of_interior r hs hs')
  obtain ⟨j, c, A, B, φ, hφ, hc, hc', hAB,
      hlevels, hGamma, hPhi⟩ :=
    fixedLevelForwardCompactifiedResidualLimit r a b
      (fun n => (hfeasible n).1)
      (fun n => levelRate_minimizing_sequence_bddAbove hanti n)
  have hclosed : s ≤ 1 - c ^ 2 * (1 - 2 * Gamma A B) :=
    compactified_certificate_residual_threshold_le
      hφ (tendsto_const_nhds (x := s))
      (fun n => (hfeasible n).2) hGamma
  have hmin : levelRate r s = Phi A B - Real.logb 2 c :=
    tendsto_nhds_unique (hlimit.comp hφ.tendsto_atTop) hPhi
  exact ⟨j, c, A, B, hc, hc', hAB, hlevels, hclosed, hmin⟩
end MetricCodes.Spherical.HigherHierarchy
