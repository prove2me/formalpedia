-- Prove2me | solution 1 for GlobalTheory.T.contracting_automorphism_subgroup_chain_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:33:06.726627+00:00
-- url     : https://prove2.me/submissions/df8bbd14-3d92-44ea-a7ab-fae07e6a15de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContractingAutomorphismSubgroupChainIndex
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContractingAutomorphismSubgroupChainIndexStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_chainIndex


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.ChainIndex := by
  first | exact @GlobalTheory.SatakeWeyl.chainIndex | exact GlobalTheory.SatakeWeyl.chainIndex | (intros; apply GlobalTheory.SatakeWeyl.chainIndex <;> assumption)
end _root_.GlobalTheory.T
