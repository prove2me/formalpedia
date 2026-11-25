-- Prove2me | solution 1 for GlobalTheory.BI.exists_isChar_eq_add_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:32.880858+00:00
-- url     : https://prove2.me/submissions/7b08afbe-db15-45ff-b561-a090e7219d1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_LinearMapShortExactCommuteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCharacterQuotientOfInjectiveIntertwining
import Theorems.Thm_GlobalTheory_T_isCharacterOverSubfield_of_representation
import Theorems.Thm_GlobalTheory_T_linear_map_short_exact_commute


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W) (f : Representation.IntertwiningMap σ ρ), Function.Injective f → ∃ c : G → L, IsChar K L c ∧ ∀ g, algebraMap K L (ρ.character g) = algebraMap K L (σ.character g) + c g := by
  intro K L _ _ _ G _ V _ _ _ W _ _ _ ρ σ f hf
  have hcomm : ∀ g, ρ g ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ σ g := fun g =>
    (f.isIntertwining' g).symm
  have hle : ∀ g, LinearMap.range f.toLinearMap ≤ (LinearMap.range f.toLinearMap).comap (ρ g) := by
    rintro g _ ⟨w, rfl⟩
    exact ⟨σ g w, (LinearMap.congr_fun (hcomm g) w).symm⟩
  refine ⟨fun g => algebraMap K L ((ρ.quotient _ hle).character g),
    (GlobalTheory.T.isCharacterOverSubfield_of_representation K L G _ (ρ.quotient _ hle)).1, fun g => ?_⟩
  rw [← map_add]
  congr 1
  refine GlobalTheory.T.linear_map_short_exact_commute K W V _ f.toLinearMap (LinearMap.range f.toLinearMap).mkQ (σ g) (ρ g)
    (ρ.quotient _ hle g) hf (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _).symm (hcomm g) ?_
  ext v
  rfl
end GlobalTheory.BI
