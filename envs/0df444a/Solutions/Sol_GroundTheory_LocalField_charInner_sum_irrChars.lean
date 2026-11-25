-- Prove2me | solution 1 for GroundTheory.LocalField.charInner_sum_irrChars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:32.772785+00:00
-- url     : https://prove2.me/submissions/8f8ce21e-84be-4201-83ab-33a4bcf7eaa6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
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
universe u
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution (c : (G → ℂ) → ℂ) {ψ : G → ℂ} (hψ : ψ ∈ irrChars G) :
    charInner G (∑ χ ∈ irrChars G, c χ • χ) ψ = c ψ := by
  classical
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_eq_single ψ]
  · rw [charInner_of_isIrrCharacter (mem_irrChars.mp hψ) (mem_irrChars.mp hψ), if_pos rfl, smul_eq_mul,
      mul_one]
  · intro χ hχ hne
    rw [charInner_of_isIrrCharacter (mem_irrChars.mp hχ) (mem_irrChars.mp hψ), if_neg hne, smul_zero]
  · intro h
    exact absurd hψ h
end GroundTheory.LocalField
