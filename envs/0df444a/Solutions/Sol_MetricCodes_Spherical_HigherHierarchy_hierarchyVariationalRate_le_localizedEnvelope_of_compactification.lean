-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_le_localizedEnvelope_of_compactification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/cf528b7d-2c22-48d1-9873-425cdf2eddd3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactificationCapFactor_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactificationCapFactor_lt_one
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_neg_logb_compactificationCapFactor_eq_sliceCost
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactificationCapFactor_scaled_spectral
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_localizedEnvelope_of_transfer

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
set_option autoImplicit false
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    (hcompact : GenuineCompactifiedHierarchyTransfer)
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    hierarchyVariationalRate s ≤
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s := by
  apply hierarchyVariationalRate_le_localizedEnvelope_of_transfer hs hs'
  intro t ht hts a b hab hgap
  have hfactor :
      0 < compactificationCapFactor s t :=
    compactificationCapFactor_pos hs' hts.le
  have hfactor' :
      compactificationCapFactor s t < 1 :=
    compactificationCapFactor_lt_one hs' hts
  have hscaled :
      s < 1 - compactificationCapFactor s t ^ 2 *
        (1 - 2 * Gamma a b) :=
    compactificationCapFactor_scaled_spectral hs' hts.le hgap
  calc
    hierarchyVariationalRate s ≤
        Phi a b - Real.logb 2 (compactificationCapFactor s t) :=
      hcompact hfactor hfactor' a b hab hscaled
    _ = Phi a b +
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t := by
      rw [← neg_logb_compactificationCapFactor_eq_sliceCost hs' hts.le]
      ring
end MetricCodes.Spherical.HigherHierarchy
