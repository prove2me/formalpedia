-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localizedLevelRate_succ_lt_of_compactifiedCertificateClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/51e9de18-f49f-414d-b776-78497174792e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_lowerSemicontinuousOn_of_compactifiedCertificateClosure
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localizedEnvelope_levelRate_succ_lt_of_lowerSemicontinuous

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
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hstrict : ∀ t ∈ Set.Ioc (0 : ℝ) s,
      levelRate (r + 1) t < levelRate r t)
    (hclosure : FixedLevelCompactifiedCertificateClosure r) :
    localizedLevelRate (r + 1) s < localizedLevelRate r s := by
  change
    MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate (r + 1)) s <
      MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
        (levelRate r) s
  exact localizedEnvelope_levelRate_succ_lt_of_lowerSemicontinuous hs hs'
    (levelRate_lowerSemicontinuousOn_of_compactifiedCertificateClosure
      hs.le hs' hclosure)
    hstrict
end MetricCodes.Spherical.HigherHierarchy
