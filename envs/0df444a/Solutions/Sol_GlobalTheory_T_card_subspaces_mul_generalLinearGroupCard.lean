-- Prove2me | solution 1 for GlobalTheory.T.card_subspaces_mul_generalLinearGroupCard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:51:17.719716+00:00
-- url     : https://prove2.me/submissions/f3e52417-b722-49a8-b98e-fb2573d51f5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCard
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCardStatement
import Theorems.Thm_GlobalTheory_CuspGL_card_subspaces_mul_glCard


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → (Nat.card {W : Submodule F V // Module.finrank F W = a} : ℂ) * (Nat.card F : ℂ) ^ (a * (Module.finrank F V - a)) * glCard F a * glCard F (Module.finrank F V - a) = glCard F (Module.finrank F V) := by
  first | exact @GlobalTheory.CuspGL.card_subspaces_mul_glCard | exact GlobalTheory.CuspGL.card_subspaces_mul_glCard | (intros; apply GlobalTheory.CuspGL.card_subspaces_mul_glCard <;> assumption)
end _root_.GlobalTheory.T
