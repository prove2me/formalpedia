-- Prove2me | solution 1 for GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:06.862913+00:00
-- url     : https://prove2.me/submissions/80d75617-bd29-4feb-89d0-3ae295d8db7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement
import Theorems.Thm_GlobalTheory_CuspGL_isPrimitive_extZero_of_sum_unipotent


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), IsChar ℂ ℂ χ → (∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, χ u = 0) → IsPrimitive (extZero χ) := by
  first | exact @GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent | exact GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent | (intros; apply GlobalTheory.CuspGL.isPrimitive_extZero_of_sum_unipotent <;> assumption)
end _root_.GlobalTheory.T
