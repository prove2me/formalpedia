-- Prove2me | solution 1 for MetricCodes.Spherical.variationalRate_lt_classical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/a3046921-199e-4047-af1d-c4dd10db7d5f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Johnson_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Spherical_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Spherical_exists_strict_improving_spherical_feasible

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
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    variationalRate s <
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  obtain ⟨a, b, hf, hcost⟩ :=
    exists_strict_improving_spherical_feasible hs hs'
  exact lt_of_le_of_lt (variationalRate_le_of_feasible hf) hcost
end MetricCodes.Spherical
