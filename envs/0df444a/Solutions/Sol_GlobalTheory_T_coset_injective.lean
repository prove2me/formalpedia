-- Prove2me | solution 1 for GlobalTheory.T.coset_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:05:16.195658+00:00
-- url     : https://prove2.me/submissions/9f8e057e-3ff3-4b50-ac86-48a3d16519d7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetInjectiveStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_cosetInj


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
theorem _root_.solution : CosetInj := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetInj | exact GlobalTheory.CompanionTheory.InertZeta.cosetInj | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetInj <;> assumption)
end _root_.GlobalTheory.T
