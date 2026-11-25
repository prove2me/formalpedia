-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_indFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:40:18.627064+00:00
-- url     : https://prove2.me/submissions/7b59dc93-cb15-4279-aa91-92b377b85e02

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_isClassFun
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_isCharacter
import Theorems.Thm_GroundTheory_LocalField_eq_of_isClassFun_of_charInner
import Theorems.Thm_GroundTheory_LocalField_mem_irrChars


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
variable {G H K : Type*} [Group G] [Group H] [Group K] [Fintype G] [Fintype H] [Fintype K]
namespace GroundTheory.LocalField
theorem _root_.solution (φ : H →* G) (φ' : K →* H) (ψ : K → ℂ) :
    indFun φ (indFun φ' ψ) = indFun (φ.comp φ') ψ := by
  apply eq_of_isClassFun_of_charInner (isClassFun_indFun _ _) (isClassFun_indFun _ _)
  intro χ hχ
  have hcl := (mem_irrChars.mp hχ).isCharacter.isClassFun
  rw [charInner_indFun _ _ hcl, charInner_indFun _ _ (hcl.comp φ), charInner_indFun _ _ hcl]
  rfl
end GroundTheory.LocalField
