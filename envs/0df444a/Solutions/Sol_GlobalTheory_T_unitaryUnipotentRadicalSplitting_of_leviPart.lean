-- Prove2me | solution 1 for GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:21:21.470826+00:00
-- url     : https://prove2.me/submissions/85f090e7-b314-47a6-a8d8-0e997d77f8c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryUnipotentRadicalSplittingOfLeviPart
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryUnipotentRadicalSplittingOfLeviPartStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_unipSplit_of_leviPart


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.LeviPart → GlobalTheory.SatakeWeyl.UnipSplit := by
  first | exact @GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | exact GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | (intros; apply GlobalTheory.SatakeWeyl.unipSplit_of_leviPart <;> assumption)
end _root_.GlobalTheory.T
