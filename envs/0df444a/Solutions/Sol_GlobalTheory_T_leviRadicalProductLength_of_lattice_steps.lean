-- Prove2me | solution 1 for GlobalTheory.T.leviRadicalProductLength_of_lattice_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:01.529145+00:00
-- url     : https://prove2.me/submissions/2e0c88b1-07ba-4060-b5a0-513d7d517c53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviRadicalProductLengthOfLatticeSteps
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviRadicalProductLengthOfLatticeStepsStatement

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
theorem _root_.solution : AddVec → Dual → SpanEq → Heis → Pointwise := by
  first | exact @GlobalTheory.InertZeta.pointwise_of_steps | exact GlobalTheory.InertZeta.pointwise_of_steps | (intros; apply GlobalTheory.InertZeta.pointwise_of_steps <;> assumption)
end _root_.GlobalTheory.T
