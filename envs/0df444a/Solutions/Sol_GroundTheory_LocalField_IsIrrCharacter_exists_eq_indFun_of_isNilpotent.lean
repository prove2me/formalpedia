-- Prove2me | solution 1 for GroundTheory.LocalField.IsIrrCharacter.exists_eq_indFun_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:28.542837+00:00
-- url     : https://prove2.me/submissions/b81d9b70-33d1-4b00-a96a-819a87a53eb1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionMonomial
import Theorems.Thm_GroundTheory_LocalField_exists_eq_indFun_of_isNilpotent_of_card

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
open Classical
namespace GroundTheory.LocalField
namespace IsIrrCharacter
theorem _root_.solution {G : Type*} [Group G] [Fintype G]
    [Group.IsNilpotent G] {χ : G → ℂ} (h : IsIrrCharacter χ) :
    ∃ (K : Subgroup G) (l : K →* ℂˣ), χ = indFun K.subtype (fun k ↦ (l k : ℂ)) :=
  exists_eq_indFun_of_isNilpotent_of_card _ G rfl h
end IsIrrCharacter
end GroundTheory.LocalField
