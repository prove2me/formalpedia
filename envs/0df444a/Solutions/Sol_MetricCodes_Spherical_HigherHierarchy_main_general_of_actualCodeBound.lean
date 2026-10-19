-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.main_general_of_actualCodeBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/b0db3671-a865-4be1-b22f-9ea5288cde1d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sphericalCodeRate_le_closedHierarchyVariationalRate_of_code_bound

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
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ {r : ℕ} {R : ℝ}
      (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b → s < 2 * Gamma a b → Phi a b < R →
        ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
          (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ))) ∧
      sphericalCodeRate s ≤ closedHierarchyVariationalRate s := by
  constructor
  · intro r R a b hinter hspectral hR
    exact hcode hs hs' a b hinter hspectral hR
  · exact sphericalCodeRate_le_closedHierarchyVariationalRate_of_code_bound
      hcode hs hs'
end MetricCodes.Spherical.HigherHierarchy
