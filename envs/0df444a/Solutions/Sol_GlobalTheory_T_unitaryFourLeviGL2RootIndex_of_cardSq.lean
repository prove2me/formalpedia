-- Prove2me | solution 1 for GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:27.153547+00:00
-- url     : https://prove2.me/submissions/ba9bce2f-f3fa-4aa8-ba90-22572a9c53cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSq
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2RootIndexOfCardSqStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_IdxFour_indexFour


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.IndexFour := by
  first | exact @GlobalTheory.SatakeWeyl.IdxFour.indexFour | exact GlobalTheory.SatakeWeyl.IdxFour.indexFour | (intros; apply GlobalTheory.SatakeWeyl.IdxFour.indexFour <;> assumption)
end _root_.GlobalTheory.T
