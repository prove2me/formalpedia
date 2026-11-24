-- Prove2me | solution 1 for GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:06:56.5688+00:00
-- url     : https://prove2.me/submissions/89305cbc-c2ad-4d7f-8ddd-9dfcdd08b310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterInnerEqIntMulCard
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterInnerEqIntMulCardStatement
import Theorems.Thm_GlobalTheory_BI_finsum_mul_star_virt_int


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
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ), a ∈ Virt ℂ ℂ G → b ∈ Virt ℂ ℂ G → ∃ m : ℤ, ∑ᶠ g, a g * star (b g) = m * (Nat.card G : ℂ) := by
  first | exact @GlobalTheory.BI.finsum_mul_star_virt_int | exact GlobalTheory.BI.finsum_mul_star_virt_int | (intros; apply GlobalTheory.BI.finsum_mul_star_virt_int <;> assumption)
end _root_.GlobalTheory.T
