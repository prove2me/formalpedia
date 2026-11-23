-- Prove2me | solution 1 for GroundTheory.LocalField.isCharacter_character
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:21.736566+00:00
-- url     : https://prove2.me/submissions/4b6f537b-84e6-44e2-b84f-87d73fc0c27e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters

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
theorem _root_.solution (ρ : Representation ℂ G V) : IsCharacter ρ.character := by
  let e := (Module.finBasis ℂ V).equivFun
  exact ⟨Fin (finrank ℂ V) → ℂ, inferInstance, inferInstance, inferInstance, conjRep ρ e,
    (char_iso (conjRepEquiv ρ e)).symm⟩
end GroundTheory.LocalField
