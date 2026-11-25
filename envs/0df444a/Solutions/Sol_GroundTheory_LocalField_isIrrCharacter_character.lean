-- Prove2me | solution 1 for GroundTheory.LocalField.isIrrCharacter_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:46.331797+00:00
-- url     : https://prove2.me/submissions/2020f057-a1ce-4c16-ad63-4bf65c34b495

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_isIrreducible_of_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
universe u
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
omit [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    IsIrrCharacter ρ.character := by
  let e := (Module.finBasis ℂ V).equivFun
  exact ⟨Fin (finrank ℂ V) → ℂ, inferInstance, inferInstance, inferInstance, conjRep ρ e,
    isIrreducible_of_equiv (conjRepEquiv ρ e), (char_iso (conjRepEquiv ρ e)).symm⟩
end GroundTheory.LocalField
