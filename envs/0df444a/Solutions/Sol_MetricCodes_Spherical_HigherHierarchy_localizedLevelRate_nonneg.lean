-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localizedLevelRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/eb9945d7-2dcb-4169-99db-d2593e411bda

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_SidelnikovLocalization_sliceCost_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_nonneg_all

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
    (hs : 0 ≤ s) (hs' : s < 1) :
    0 ≤ localizedLevelRate r s := by
  unfold localizedLevelRate
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
  apply le_csInf (Set.Nonempty.image _ (Set.nonempty_Icc.mpr hs))
  rintro _ ⟨t, ht, rfl⟩
  exact add_nonneg (levelRate_nonneg_all r t)
    (MetricCodes.Spherical.SidelnikovLocalization.sliceCost_nonneg ht.2 hs')
end MetricCodes.Spherical.HigherHierarchy
