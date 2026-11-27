-- Prove2me | solution 1 for GlobalTheory.T.unitarySatake_weylInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:26.728223+00:00
-- url     : https://prove2.me/submissions/8cdf501a-a3a4-441b-aea1-2fc044d141d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeWeylInvariant
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitarySatakeWeylInvariantStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_satWeyl


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
theorem _root_.solution : Formalism.UG.SatWeyl := by
  first | exact @GlobalTheory.SatakeWeyl.satWeyl | exact GlobalTheory.SatakeWeyl.satWeyl | (intros; apply GlobalTheory.SatakeWeyl.satWeyl <;> assumption)
end _root_.GlobalTheory.T
