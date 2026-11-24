-- Prove2me | solution 1 for GlobalTheory.T.pointwise_of_span_heisenberg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:17.093038+00:00
-- url     : https://prove2.me/submissions/25474cfe-9cb9-43bc-9a49-47f15feec11e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenberg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_PointwiseOfSpanHeisenbergStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLen_pointwise


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
  first | exact @GlobalTheory.CompanionTheory.InertLen.pointwise | exact GlobalTheory.CompanionTheory.InertLen.pointwise | (intros; apply GlobalTheory.CompanionTheory.InertLen.pointwise <;> assumption)
end _root_.GlobalTheory.T
