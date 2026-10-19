-- Prove2me | solution 1 for MetricCodes.MRRW.strict_mrrw2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/0063e876-2362-4943-aad1-60b35087e64b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_mrrw_endpoint_dichotomy
import Theorems.Thm_MetricCodes_Johnson_combinedVariationalRate_le_shell
import Theorems.Thm_MetricCodes_Johnson_combinedVariationalRate_lt_mrrw_of_endpoint
import Theorems.Thm_MetricCodes_MRRW_variationalRate_lt_mrrw_of_interior

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    MetricCodes.Johnson.combinedVariationalRate δ <
      MetricCodes.Johnson.mrrwRate δ := by
  rcases MetricCodes.Johnson.mrrw_endpoint_dichotomy hδ hhalf with
    hstrict | hendpoint
  · exact
      (MetricCodes.Johnson.combinedVariationalRate_le_shell δ).trans_lt
        (variationalRate_lt_mrrw_of_interior hδ hhalf hstrict)
  · exact MetricCodes.Johnson.combinedVariationalRate_lt_mrrw_of_endpoint
      hδ hhalf hendpoint
end MetricCodes.MRRW
