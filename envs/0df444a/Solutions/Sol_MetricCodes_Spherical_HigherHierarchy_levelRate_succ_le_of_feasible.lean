-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_succ_le_of_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/97c80ffa-8a61-4670-b8d2-706ce66457be

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_nextLevel_feasible_lt

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
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ} {s : ℝ}
    (hs : 0 < s) (h : (levelRateSet r s).Nonempty) :
    levelRate (r + 1) s ≤ levelRate r s := by
  unfold levelRate
  apply le_csInf h
  rintro _ ⟨a, b, hinterlacing, hgap, rfl⟩
  obtain ⟨A, B, hAB, hgapAB, hPhi⟩ :=
    exists_nextLevel_feasible_lt hs hinterlacing hgap
  exact (levelRate_le hAB hgapAB).trans hPhi.le
end MetricCodes.Spherical.HigherHierarchy
