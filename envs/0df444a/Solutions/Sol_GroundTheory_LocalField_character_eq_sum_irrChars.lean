-- Prove2me | solution 1 for GroundTheory.LocalField.character_eq_sum_irrChars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:04.902664+00:00
-- url     : https://prove2.me/submissions/b48544c5-e53f-4d15-bccd-c5a4a002d5b5

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_character_eq_sum_irrChars_of_finrank

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
namespace GroundTheory.LocalField
theorem _root_.solution {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.character = ∑ ψ ∈ irrChars G, charInner G ρ.character ψ • ψ :=
  character_eq_sum_irrChars_of_finrank _ V ρ rfl
end GroundTheory.LocalField
