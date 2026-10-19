-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_le_compactified_datum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/c7abb538-b2eb-4bc7-a1b6-553f1e018dee

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_le
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_succ_le_compactified_certificate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_antitone_level

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
    {k j : ℕ} {s c : ℝ}
    (hs : 0 < s) (hs' : s < 1)
    (hc : 0 < c)
    (a : Fin (j + 1) → ℝ) (b : Fin j → ℝ)
    (h : Interlacing a b)
    (hscaled : s < 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hlevels : (c = 1 ∧ j ≤ k) ∨ (c < 1 ∧ j + 1 ≤ k)) :
    levelRate k s ≤ Phi a b - Real.logb 2 c := by
  rcases hlevels with ⟨rfl, hjk⟩ | ⟨hc', hjk⟩
  · have hgap : s < 2 * Gamma a b := by
      norm_num at hscaled ⊢
      linarith
    simpa using (levelRate_antitone_level hs hs' hjk).trans
      (levelRate_le h hgap)
  · exact (levelRate_antitone_level hs hs' hjk).trans
      (levelRate_succ_le_compactified_certificate hc hc' a b h hscaled)
end MetricCodes.Spherical.HigherHierarchy
