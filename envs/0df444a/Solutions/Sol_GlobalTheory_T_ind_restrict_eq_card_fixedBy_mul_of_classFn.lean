-- Prove2me | solution 1 for GlobalTheory.T.ind_restrict_eq_card_fixedBy_mul_of_classFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:13:35.447821+00:00
-- url     : https://prove2.me/submissions/e077a3e1-4ba9-4c2b-ac02-17e9bc87a9a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndRestrictEqCardFixedByMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndRestrictEqCardFixedByMulStatement
import Theorems.Thm_GlobalTheory_BI_ind_restrict_eq_card_fixedBy_mul


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
theorem _root_.solution : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by
  first | exact @GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul | exact GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul | (intros; apply GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul <;> assumption)
end _root_.GlobalTheory.T
