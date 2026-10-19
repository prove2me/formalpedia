-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.strict_hierarchy_of_codeBound_strictLevelRates_and_compactifiedClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/0befc190-0e49-43f8-b28e-4018430ba170

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_strict_hierarchy_of_codeBound_pointwiseStrict_and_compactifiedClosure

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
    (hlevel : ∀ (r : ℕ) {t : ℝ}, 0 < t → t < 1 →
      levelRate (r + 1) t < levelRate r t)
    (hclosure : ∀ r : ℕ, FixedLevelCompactifiedCertificateClosure r)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (∀ r : ℕ,
      levelRate (r + 1) s < levelRate r s ∧
        localizedLevelRate (r + 1) s < localizedLevelRate r s) ∧
      sphericalCodeRate s ≤ localizedHierarchyRate s ∧
      localizedHierarchyRate s < localizedLevelRate 1 s ∧
      localizedLevelRate 1 s < localizedRowRate s ∧
      localizedRowRate s < localizedLevelRate 0 s ∧
      localizedLevelRate 0 s = classicalLocalizedRate s := by
  apply strict_hierarchy_of_codeBound_pointwiseStrict_and_compactifiedClosure
    hs hs' hcode (hclosure := hclosure)
  intro r t ht hts
  exact hlevel r ht (lt_of_le_of_lt hts hs')
end MetricCodes.Spherical.HigherHierarchy
