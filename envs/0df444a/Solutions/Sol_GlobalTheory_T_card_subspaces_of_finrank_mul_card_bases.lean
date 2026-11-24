-- Prove2me | solution 1 for GlobalTheory.T.card_subspaces_of_finrank_mul_card_bases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:24:43.033188+00:00
-- url     : https://prove2.me/submissions/ee9d421d-6dc8-4fb1-af48-39b0a9840305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBases
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBasesStatement
import Theorems.Thm_GlobalTheory_SubspaceNumber_card_subspaces_mul


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (a : ℕ), a ≤ Module.finrank F V → Nat.card {W : Submodule F V // Module.finrank F W = a} * ∏ i ∈ Finset.range a, (Nat.card F ^ a - Nat.card F ^ i) = ∏ i ∈ Finset.range a, (Nat.card F ^ Module.finrank F V - Nat.card F ^ i) := by
  first | exact @GlobalTheory.SubspaceNumber.card_subspaces_mul | exact GlobalTheory.SubspaceNumber.card_subspaces_mul | (intros; apply GlobalTheory.SubspaceNumber.card_subspaces_mul <;> assumption)
end _root_.GlobalTheory.T
