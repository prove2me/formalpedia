-- Prove2me | solution 1 for GroundTheory.LocalField.IsIrrCharacter.isCharacter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:56.726825+00:00
-- url     : https://prove2.me/submissions/6fce1814-4600-4b17-b2d7-54908fd1f23a

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
omit [Fintype G]
namespace GroundTheory.LocalField
namespace IsIrrCharacter
theorem _root_.solution {χ : G → ℂ} (h : IsIrrCharacter χ) : IsCharacter χ := by
  obtain ⟨V, _, _, _, ρ, _, rfl⟩ := h
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, rfl⟩
end IsIrrCharacter
end GroundTheory.LocalField
