-- Prove2me | solution 1 for GlobalTheory.T.small_corner_of_heisenberg_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:27.999312+00:00
-- url     : https://prove2.me/submissions/36831924-7241-456f-b176-03640dc9f1a6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallCornerOfHeisenbergDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallCornerOfHeisenbergDualStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_smallCorner_of_heis


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
theorem _root_.solution : Heis → Dual → SmallCorner := by
  first | exact @GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis | exact GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis | (intros; apply GlobalTheory.CompanionTheory.InertCorner.smallCorner_of_heis <;> assumption)
end _root_.GlobalTheory.T
