-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.strict_hierarchy_of_codeBound_pointwiseStrict_and_compactifiedClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/f0ebedbd-c217-4343-9f67-61211c44c529

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sphericalCodeRate_le_localizedHierarchyRate_of_codeBound
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedLevelRate_one_lt_localizedRowRate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedRowRate_lt_localizedLevelRate_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_strict_hierarchy_of_components
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedLevelRate_succ_lt_of_compactifiedCertificateClosure

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
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hcode : FixedLevelHierarchyCodeBound)
    (hlevel : ∀ (r : ℕ) (t : ℝ), 0 < t → t ≤ s →
      levelRate (r + 1) t < levelRate r t)
    (hclosure : ∀ r : ℕ, FixedLevelCompactifiedCertificateClosure r) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s := by
  apply strict_hierarchy_of_components hs hs'
  · intro r
    exact hlevel r s hs le_rfl
  · intro r
    exact localizedLevelRate_succ_lt_of_compactifiedCertificateClosure
      hs hs' (fun t ht => hlevel r t ht.1 ht.2) (hclosure r)
  · exact sphericalCodeRate_le_localizedHierarchyRate_of_codeBound
      hcode hs hs'
  · exact localizedLevelRate_one_lt_localizedRowRate hs hs'
  · exact localizedRowRate_lt_localizedLevelRate_zero hs hs'
end MetricCodes.Spherical.HigherHierarchy
