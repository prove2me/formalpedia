-- Prove2me | solution 1 for MetricCodes.Johnson.main_binary_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/86dfc4a7-e263-4983-821d-2be5fde33d95

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_strict_mrrw2
import Theorems.Thm_MetricCodes_Johnson_binaryRate_le_combinedVariationalRate

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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Filter Topology
open scoped Topology
open MetricCodes MetricCodes.Johnson
namespace MetricCodes.Johnson
theorem _root_.solution {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    MetricCodes.Hamming.binaryRate δ ≤ combinedVariationalRate δ ∧
      combinedVariationalRate δ < mrrwRate δ :=
  ⟨binaryRate_le_combinedVariationalRate hδ hhalf,
    MetricCodes.MRRW.strict_mrrw2 hδ hhalf⟩
end MetricCodes.Johnson
