-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.strict_hierarchy_of_fixedLevelCodeBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/d4a9f07a-9648-4bf9-ac45-90918e51f95c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_fixedLevelCompactifiedCertificateClosure
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_succ_lt
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_strict_hierarchy_of_codeBound_strictLevelRates_and_compactifiedClosure

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
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s := by
  exact strict_hierarchy_of_codeBound_strictLevelRates_and_compactifiedClosure
    hcode (fun r {t} ht ht' => levelRate_succ_lt (r := r) (s := t) ht ht')
    fixedLevelCompactifiedCertificateClosure hs hs'
end MetricCodes.Spherical.HigherHierarchy
