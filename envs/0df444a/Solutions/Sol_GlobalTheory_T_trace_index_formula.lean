-- Prove2me | solution 1 for GlobalTheory.T.trace_index_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:47.912873+00:00
-- url     : https://prove2.me/submissions/deb952fa-8bc8-4206-afff-36c77675fcd4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_TraceIndexFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_TraceIndexFormulaStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_traceIndex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : TraceIndex := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.traceIndex | exact GlobalTheory.CompanionTheory.InertZeta.traceIndex | (intros; apply GlobalTheory.CompanionTheory.InertZeta.traceIndex <;> assumption)
end _root_.GlobalTheory.T
