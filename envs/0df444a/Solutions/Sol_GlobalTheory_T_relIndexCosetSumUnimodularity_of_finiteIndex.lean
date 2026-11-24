-- Prove2me | solution 1 for GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:06:47.880169+00:00
-- url     : https://prove2.me/submissions/0d1558a5-276f-4b47-8b8e-c8c72244eb10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCosetSumUnimodularityOfFiniteIndex
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexCosetSumUnimodularityOfFiniteIndexStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_unimod_of_unimodFin


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.UnimodFin → GlobalTheory.SatakeWeyl.Unimod := by
  first | exact @GlobalTheory.SatakeWeyl.unimod_of_unimodFin | exact GlobalTheory.SatakeWeyl.unimod_of_unimodFin | (intros; apply GlobalTheory.SatakeWeyl.unimod_of_unimodFin <;> assumption)
end _root_.GlobalTheory.T
