-- Prove2me | solution 1 for GlobalTheory.T.small_corner_of_heisenberg_duality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:17.347923+00:00
-- url     : https://prove2.me/submissions/32fbde53-091e-48c5-bc92-6a924fbb9af2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallCornerOfHeisenbergDuality
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallCornerOfHeisenbergDualityStatement
import Theorems.Thm_GlobalTheory_InertZeta_smallCorner_of_heis_dual


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
  first | exact @GlobalTheory.InertZeta.smallCorner_of_heis_dual | exact GlobalTheory.InertZeta.smallCorner_of_heis_dual | (intros; apply GlobalTheory.InertZeta.smallCorner_of_heis_dual <;> assumption)
end _root_.GlobalTheory.T
