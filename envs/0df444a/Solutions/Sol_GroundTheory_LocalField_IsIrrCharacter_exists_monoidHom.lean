-- Prove2me | solution 1 for GroundTheory.LocalField.IsIrrCharacter.exists_monoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:21.39043+00:00
-- url     : https://prove2.me/submissions/bbba6f00-90e4-4010-8a7f-76bf3a5dc967

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Theorems.Thm_GroundTheory_LocalField_eq_trace_smul_id_of_finrank_eq_one

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
variable {G : Type*} [Group G] [IsMulCommutative G]
namespace GroundTheory.LocalField
namespace IsIrrCharacter
theorem _root_.solution {χ : G → ℂ} (h : IsIrrCharacter χ) :
    ∃ l : G →* ℂˣ, ∀ g, χ g = l g := by
  obtain ⟨V, _, _, _, ρ, hρ, rfl⟩ := h
  have h1 : finrank ℂ V = 1 := IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  have hmul : ∀ g k, ρ.character (g * k) = ρ.character g * ρ.character k := by
    intro g k
    have hg := eq_trace_smul_id_of_finrank_eq_one h1 (ρ g)
    have hk := eq_trace_smul_id_of_finrank_eq_one h1 (ρ k)
    simp only [Representation.character, map_mul]
    conv_lhs => rw [hg, hk]
    rw [smul_mul_smul, map_smul, Module.End.mul_eq_comp, LinearMap.id_comp, LinearMap.trace_id, h1]
    simp
  let f : G →* ℂ :=
    { toFun := ρ.character
      map_one' := by rw [char_one, h1]; simp
      map_mul' := hmul }
  exact ⟨f.toHomUnits, fun g ↦ rfl⟩
end IsIrrCharacter
end GroundTheory.LocalField
