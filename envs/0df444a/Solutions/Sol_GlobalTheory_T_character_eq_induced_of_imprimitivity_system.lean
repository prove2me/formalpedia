-- Prove2me | solution 1 for GlobalTheory.T.character_eq_induced_of_imprimitivity_system
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:49:47.346264+00:00
-- url     : https://prove2.me/submissions/0bce8efa-c3de-45d9-aaf6-c49030ec4e04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterEqInducedOfImprimitivitySystem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterEqInducedOfImprimitivitySystemStatement
import Theorems.Thm_GlobalTheory_BI_character_eq_ind_of_imprimitive


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
theorem _root_.solution : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V) (T : Subgroup G) (e : Module.End L V), ρ.IsIrreducible → e ≠ 0 → e * e = e → (∀ t ∈ T, ρ t * e = e * ρ t) → (∀ g ∉ T, e * ρ g * e = 0) → ∃ ψ : T → L, IsChar L L ψ ∧ ∀ g, ρ.character g = ind T ψ g := by
  first | exact @GlobalTheory.BI.character_eq_ind_of_imprimitive | exact GlobalTheory.BI.character_eq_ind_of_imprimitive | (intros; apply GlobalTheory.BI.character_eq_ind_of_imprimitive <;> assumption)
end _root_.GlobalTheory.T
