-- Prove2me | solution 1 for GlobalTheory.T.integralLatticeInverseIndex_of_elementaryDivisors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:50.485157+00:00
-- url     : https://prove2.me/submissions/2adf4c01-ed12-441a-9f6d-828a48454d4b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralLatticeInverseIndexOfElementaryDivisors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralLatticeInverseIndexOfElementaryDivisorsStatement
import Theorems.Thm_GlobalTheory_InertZeta_latIndex_of_smith


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
theorem _root_.solution : Smith → LatIndex := by
  first | exact @GlobalTheory.InertZeta.latIndex_of_smith | exact GlobalTheory.InertZeta.latIndex_of_smith | (intros; apply GlobalTheory.InertZeta.latIndex_of_smith <;> assumption)
end _root_.GlobalTheory.T
