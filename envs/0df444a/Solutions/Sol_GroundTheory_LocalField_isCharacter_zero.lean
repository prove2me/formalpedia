-- Prove2me | solution 1 for GroundTheory.LocalField.isCharacter_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:22.104657+00:00
-- url     : https://prove2.me/submissions/ab6b3fca-d3a4-42bf-9286-2bfdd8b96ecd

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
variable {G : Type*} [Group G]
namespace GroundTheory.LocalField
theorem _root_.solution : IsCharacter (0 : G → ℂ) := by
  refine ⟨PUnit, inferInstance, inferInstance, inferInstance, Representation.trivial ℂ G PUnit, ?_⟩
  funext g
  have : (Representation.trivial ℂ G PUnit) g = 0 := LinearMap.ext fun v ↦ Subsingleton.elim _ _
  simp [Representation.character, this]
end GroundTheory.LocalField
