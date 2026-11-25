-- Prove2me | solution 1 for GlobalTheory.T.virtualCharacter_irreducible_expansion_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:52.330129+00:00
-- url     : https://prove2.me/submissions/7fcbae8e-d869-4c21-9cdd-ab087b7af692

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterIrreducibleExpansionNormSqStatement
import Theorems.Thm_GlobalTheory_BI_virt_expand


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
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, IsIrrChar ℂ ℂ χ) ∧ φ = c.sum (fun χ m => m • χ) ∧ ∑ᶠ g, φ g * star (φ g) = (c.sum fun _ m => (m : ℂ) ^ 2) * (Nat.card G : ℂ) := by
  first | exact @GlobalTheory.BI.virt_expand | exact GlobalTheory.BI.virt_expand | (intros; apply GlobalTheory.BI.virt_expand <;> assumption)
end _root_.GlobalTheory.T
