-- Prove2me | solution 1 for GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:22:29.421139+00:00
-- url     : https://prove2.me/submissions/e47f8519-4588-4343-8925-79c85bf82084

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2CartanDoubleCosets
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryFourLeviGL2CartanDoubleCosetsStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_Four_cartanFour


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
theorem _root_.solution : GlobalTheory.SatakeWeyl.CartanFour := by
  first | exact @GlobalTheory.SatakeWeyl.Four.cartanFour | exact GlobalTheory.SatakeWeyl.Four.cartanFour | (intros; apply GlobalTheory.SatakeWeyl.Four.cartanFour <;> assumption)
end _root_.GlobalTheory.T
