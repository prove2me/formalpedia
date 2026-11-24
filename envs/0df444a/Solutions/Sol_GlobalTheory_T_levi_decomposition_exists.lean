-- Prove2me | solution 1 for GlobalTheory.T.levi_decomposition_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:17:05.951515+00:00
-- url     : https://prove2.me/submissions/790c3ce1-6a4e-4480-a91c-dd754dfd425b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LeviDecompositionExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LeviDecompositionExistsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_leviExists


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
theorem _root_.solution : LeviExists := by
  first | exact @GlobalTheory.CompanionTheory.InertLevi.leviExists | exact GlobalTheory.CompanionTheory.InertLevi.leviExists | (intros; apply GlobalTheory.CompanionTheory.InertLevi.leviExists <;> assumption)
end _root_.GlobalTheory.T
