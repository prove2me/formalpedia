-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.isClassFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:55.961365+00:00
-- url     : https://prove2.me/submissions/dfc79cb8-c826-4b5d-9da6-7a46b5237e0c

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
variable {G : Type*} [Group G] [Fintype G]
omit [Fintype G]
namespace GroundTheory.LocalField
namespace IsCharacter
theorem _root_.solution {χ : G → ℂ} (h : IsCharacter χ) : IsClassFun χ := by
  obtain ⟨V, _, _, _, ρ, rfl⟩ := h
  intro g k
  exact char_conj ρ g k
end IsCharacter
end GroundTheory.LocalField
