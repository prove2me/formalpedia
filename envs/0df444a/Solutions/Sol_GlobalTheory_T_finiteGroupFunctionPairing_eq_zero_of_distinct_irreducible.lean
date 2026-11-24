-- Prove2me | solution 1 for GlobalTheory.T.finiteGroupFunctionPairing_eq_zero_of_distinct_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:40.331811+00:00
-- url     : https://prove2.me/submissions/8cebb97c-0482-481e-9943-5856f4161f8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingEqZeroOfDistinctIrreduStatement
import Theorems.Thm_GlobalTheory_BI_pair_eq_zero_of_isIrrChar_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ), IsIrrChar ℂ ℂ a → IsIrrChar ℂ ℂ b → a ≠ b → pair a b = 0 := by
  first | exact @GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne | (intros; apply GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne <;> assumption)
end _root_.GlobalTheory.T
