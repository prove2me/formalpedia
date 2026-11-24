-- Prove2me | solution 1 for GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:15:05.896845+00:00
-- url     : https://prove2.me/submissions/27334dad-0a13-422f-8e07-a4d9bd962954

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralRightInvariantEqSumOpenSubgroupCosets
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralRightInvariantEqSumOpenSubgroupCosetsStatement
import Theorems.Thm_GlobalTheory_InertZeta_cosetIntegral_holds


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
theorem _root_.solution : CosetIntegral := by
  first | exact @GlobalTheory.InertZeta.cosetIntegral_holds | exact GlobalTheory.InertZeta.cosetIntegral_holds | (intros; apply GlobalTheory.InertZeta.cosetIntegral_holds <;> assumption)
end _root_.GlobalTheory.T
