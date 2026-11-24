-- Prove2me | solution 1 for GlobalTheory.T.span_equality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:21.427863+00:00
-- url     : https://prove2.me/submissions/28b20780-610c-46ad-8ae1-2328ba269436

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEquality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SpanEqualityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertSpan_spanEq


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
theorem _root_.solution : SpanEq := by
  first | exact @GlobalTheory.CompanionTheory.InertSpan.spanEq | exact GlobalTheory.CompanionTheory.InertSpan.spanEq | (intros; apply GlobalTheory.CompanionTheory.InertSpan.spanEq <;> assumption)
end _root_.GlobalTheory.T
