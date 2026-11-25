-- Prove2me | solution 1 for GlobalTheory.T.irreducible_character_of_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:04.713124+00:00
-- url     : https://prove2.me/submissions/a28c14fc-3c25-4824-88e9-f6c8497e91e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleCharacterOfProduct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleCharacterOfProductStatement
import Theorems.Thm_GlobalTheory_irrChar_pi_eq_prod


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
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (χ : (∀ i, G i) → ℂ), IsIrrChar ℂ ℂ χ → ∃ ψ : ∀ i, G i → ℂ, (∀ i, IsIrrChar ℂ ℂ (ψ i)) ∧ ∀ x, χ x = ∏ i, ψ i (x i) := by
  first | exact @GlobalTheory.irrChar_pi_eq_prod | exact GlobalTheory.irrChar_pi_eq_prod | (intros; apply GlobalTheory.irrChar_pi_eq_prod <;> assumption)
end _root_.GlobalTheory.T
