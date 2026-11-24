-- Prove2me | solution 1 for GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:35:03.663926+00:00
-- url     : https://prove2.me/submissions/b71db8da-8cf5-461d-aa8f-4dbbfd8fce90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceZeroIntegersModUniformizerCardOfCardSq
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceZeroIntegersModUniformizerCardOfCardSqStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_traceZeroIndex_of_intIndex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.TraceZeroIndex := by
  first | exact @GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex | exact GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex | (intros; apply GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex <;> assumption)
end _root_.GlobalTheory.T
