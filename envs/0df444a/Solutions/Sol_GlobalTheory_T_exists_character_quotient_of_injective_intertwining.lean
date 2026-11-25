-- Prove2me | solution 1 for GlobalTheory.T.exists_character_quotient_of_injective_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:41.472772+00:00
-- url     : https://prove2.me/submissions/80a09fd1-4d08-4c95-89df-ef1675755901

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterQuotientOfInjectiveIntertwining
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterQuotientOfInjectiveIntertwiningStatement
import Theorems.Thm_GlobalTheory_BI_exists_isChar_eq_add_of_injective


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
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W) (f : Representation.IntertwiningMap σ ρ), Function.Injective f → ∃ c : G → L, IsChar K L c ∧ ∀ g, algebraMap K L (ρ.character g) = algebraMap K L (σ.character g) + c g := by
  first | exact @GlobalTheory.BI.exists_isChar_eq_add_of_injective | exact GlobalTheory.BI.exists_isChar_eq_add_of_injective | (intros; apply GlobalTheory.BI.exists_isChar_eq_add_of_injective <;> assumption)
end _root_.GlobalTheory.T
