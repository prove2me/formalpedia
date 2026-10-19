-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.strict_hierarchy_of_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/9a9114c5-faef-4a9d-a5c1-fd101d7dce6b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedHierarchyRate_lt_level_one_of_level_two
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedLevelRate_zero_eq_classicalLocalizedRate

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
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlevel : ∀ r : ℕ, levelRate (r + 1) s < levelRate r s)
    (hlocalized : ∀ r : ℕ,
      localizedLevelRate (r + 1) s < localizedLevelRate r s)
    (hcode : sphericalCodeRate s ≤ localizedHierarchyRate s)
    (hrow : localizedLevelRate 1 s < localizedRowRate s)
    (hclassical : localizedRowRate s < localizedLevelRate 0 s) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s := by
  refine ⟨fun r => ⟨hlevel r, hlocalized r⟩,
    hcode, ?_, hrow, hclassical,
    localizedLevelRate_zero_eq_classicalLocalizedRate hs.le hs'⟩
  exact localizedHierarchyRate_lt_level_one_of_level_two hs.le hs'
    (hlocalized 1)
end MetricCodes.Spherical.HigherHierarchy
