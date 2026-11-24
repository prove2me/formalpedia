-- Prove2me | solution 1 for GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:22.385549+00:00
-- url     : https://prove2.me/submissions/ee942878-69d2-4c9c-8a7f-b1a4b2a383e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContractingAutChainCosetSumScalingOfUnimodularit
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContractingAutChainCosetSumScalingOfUnimodularitStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_chainSum_of_unimod


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.Unimod → GlobalTheory.SatakeWeyl.ChainIndex → GlobalTheory.SatakeWeyl.ChainSum := by
  first | exact @GlobalTheory.SatakeWeyl.chainSum_of_unimod | exact GlobalTheory.SatakeWeyl.chainSum_of_unimod | (intros; apply GlobalTheory.SatakeWeyl.chainSum_of_unimod <;> assumption)
end _root_.GlobalTheory.T
