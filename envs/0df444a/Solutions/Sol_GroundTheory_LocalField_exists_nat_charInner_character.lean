-- Prove2me | solution 1 for GroundTheory.LocalField.exists_nat_charInner_character
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:56.067215+00:00
-- url     : https://prove2.me/submissions/0eabcf75-9bf9-4fd8-85c4-fa571e9d2460

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_charInner_character_character

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {ψ : G → ℂ} (hψ : IsIrrCharacter ψ) :
    ∃ m : ℕ, charInner G ρ.character ψ = m := by
  obtain ⟨W, _, _, _, σ, _, rfl⟩ := hψ
  exact ⟨_, charInner_character_character σ ρ⟩
end GroundTheory.LocalField
