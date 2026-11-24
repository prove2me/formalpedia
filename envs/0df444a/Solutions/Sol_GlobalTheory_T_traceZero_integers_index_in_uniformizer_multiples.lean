-- Prove2me | solution 1 for GlobalTheory.T.traceZero_integers_index_in_uniformizer_multiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:46.305988+00:00
-- url     : https://prove2.me/submissions/dd4a5e09-239b-473e-98d3-cfdf70ec96f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TraceZeroIntegersIndexInUniformizerMultiples
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TraceZeroIntegersIndexInUniformizerMultiplesStatement
import Theorems.Thm_GlobalTheory_InertZeta_traceIndex


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
  first | exact @GlobalTheory.InertZeta.traceIndex | exact GlobalTheory.InertZeta.traceIndex | (intros; apply GlobalTheory.InertZeta.traceIndex <;> assumption)
end _root_.GlobalTheory.T
