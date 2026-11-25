-- Prove2me | solution 1 for GlobalTheory.T.finiteGroupFunctionPairing_add_nat_pos_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:22:20.947319+00:00
-- url     : https://prove2.me/submissions/4e4a1d93-ff28-4369-9bf1-fa0135a429f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingAddNatPosSymm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FiniteGroupFunctionPairingAddNatPosSymmStatement
import Theorems.Thm_GlobalTheory_BI_pair_add_nat_pos_symm


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ a b c : G → L, pair (a + b) c = pair a c + pair b c) ∧ (∀ a b : G → L, IsChar K L a → IsChar K L b → ∃ n : ℕ, pair a b = (n : L)) ∧ (∀ φ : G → L, IsIrrChar K L φ → ∃ n : ℕ, 0 < n ∧ pair φ φ = (n : L)) ∧ ∀ a b : G → L, pair a b = pair b a := by
  first | exact @GlobalTheory.BI.pair_add_nat_pos_symm | exact GlobalTheory.BI.pair_add_nat_pos_symm | (intros; apply GlobalTheory.BI.pair_add_nat_pos_symm <;> assumption)
end _root_.GlobalTheory.T
