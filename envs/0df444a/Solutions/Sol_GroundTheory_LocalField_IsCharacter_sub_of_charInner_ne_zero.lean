-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.sub_of_charInner_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:18.608305+00:00
-- url     : https://prove2.me/submissions/15efcb59-b05a-4d21-b288-11f134b572ff

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_isClassFun
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_isCharacter
import Theorems.Thm_GroundTheory_LocalField_isCharacter_iff
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
variable {G : Type*} [Group G]
variable [Fintype G]
namespace GroundTheory.LocalField
namespace IsCharacter
theorem _root_.solution {η χ : G → ℂ} (hη : IsCharacter η)
    (hχ : IsIrrCharacter χ) (h : charInner G η χ ≠ 0) : IsCharacter (η - χ) := by
  classical
  rw [isCharacter_iff]
  refine ⟨fun g k ↦ by simp [hη.isClassFun g k, hχ.isCharacter.isClassFun g k], fun ψ hψ ↦ ?_⟩
  obtain ⟨n, hn⟩ := hη.exists_nat_charInner (mem_irrChars.mp hψ).isCharacter
  rw [map_sub, LinearMap.sub_apply, hn, charInner_of_isIrrCharacter hχ (mem_irrChars.mp hψ)]
  split_ifs with he
  · subst he
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact h (by rw [hn, Nat.cast_zero])
    exact ⟨n - 1, by rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn0), Nat.cast_one]⟩
  · exact ⟨n, by rw [sub_zero]⟩
end IsCharacter
end GroundTheory.LocalField
