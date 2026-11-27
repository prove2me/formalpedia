-- Prove2me | solution 1 for GlobalTheory.T.polarisation_dual_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:33.243571+00:00
-- url     : https://prove2.me/submissions/91cd498a-1c9e-480e-afa9-9b90d31df85b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarisationDualStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarisationDualStatementStatement
import Theorems.Thm_GlobalTheory_CMLatticeRow_statement


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement := by
  first | exact @GlobalTheory.CMLatticeRow.statement | exact GlobalTheory.CMLatticeRow.statement | (intros; apply GlobalTheory.CMLatticeRow.statement <;> assumption)
end _root_.GlobalTheory.T
