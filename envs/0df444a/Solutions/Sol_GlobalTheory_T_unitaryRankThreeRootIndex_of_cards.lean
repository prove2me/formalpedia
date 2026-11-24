-- Prove2me | solution 1 for GlobalTheory.T.unitaryRankThreeRootIndex_of_cards
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:21:20.060098+00:00
-- url     : https://prove2.me/submissions/542dc4bc-f7f4-4473-ac27-355c90236368

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCards
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryRankThreeRootIndexOfCardsStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_Heis_indexThree


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.TraceZeroIndex → GlobalTheory.SatakeWeyl.IndexThree := by
  first | exact @GlobalTheory.SatakeWeyl.Heis.indexThree | exact GlobalTheory.SatakeWeyl.Heis.indexThree | (intros; apply GlobalTheory.SatakeWeyl.Heis.indexThree <;> assumption)
end _root_.GlobalTheory.T
