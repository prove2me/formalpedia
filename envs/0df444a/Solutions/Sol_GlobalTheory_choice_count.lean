-- Prove2me | solution 1 for GlobalTheory.choice_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:43.25266+00:00
-- url     : https://prove2.me/submissions/c8a4ae06-a94d-4cba-be87-bf4ed1bc6465

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExceptionalPrimesFiniteCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DivLeRpowThreeQuarters
import Theorems.Thm_GlobalTheory_choiceCount_of
import Theorems.Thm_GlobalTheory_exceptional_set_count
import Theorems.Thm_GlobalTheory_rootsOfUnityCount


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Formalism.CyclotomicNorms.ChoiceCount := choiceCount_of exceptional_set_count rootsOfUnityCount
end GlobalTheory
