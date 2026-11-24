-- Prove2me | solution 1 for GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:22:48.892509+00:00
-- url     : https://prove2.me/submissions/cdb2add2-1e1a-405e-b9b7-c82caaf58028

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumUnipotentRadicalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumUnipotentRadicalEqZeroStatement
import Theorems.Thm_GlobalTheory_CuspGL_IsPrimitive_finsum_unipotentRadical_eq_zero


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (φ : Module.End F (Fin d → F) → ℂ), IsPrimitive φ → ∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, φ (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)) = 0 := by
  first | exact @GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero | exact GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero | (intros; apply GlobalTheory.CuspGL.IsPrimitive.finsum_unipotentRadical_eq_zero <;> assumption)
end _root_.GlobalTheory.T
