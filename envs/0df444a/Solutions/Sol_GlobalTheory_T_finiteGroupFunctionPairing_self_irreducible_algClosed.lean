-- Prove2me | solution 1 for GlobalTheory.T.finiteGroupFunctionPairing_self_irreducible_algClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:30.969683+00:00
-- url     : https://prove2.me/submissions/234702da-20d3-4314-84a4-a3e51821e474

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingSelfIrreducibleAlgClosStatement
import Theorems.Thm_GlobalTheory_BI_pair_self_of_isIrrChar_algClosed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), IsIrrChar L L χ → pair χ χ = 1 := by
  first | exact @GlobalTheory.BI.pair_self_of_isIrrChar_algClosed | exact GlobalTheory.BI.pair_self_of_isIrrChar_algClosed | (intros; apply GlobalTheory.BI.pair_self_of_isIrrChar_algClosed <;> assumption)
end _root_.GlobalTheory.T
