-- Prove2me | solution 1 for GroundTheory.LocalField.charInner_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:45.133581+00:00
-- url     : https://prove2.me/submissions/25bb333c-7925-45ee-9e61-9d09e58b9cec

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
namespace GroundTheory.LocalField
theorem _root_.solution (χ ψ : G → ℂ) : charInner G χ ψ = charInner G ψ χ := by
  rw [charInner_apply, charInner_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g ↦ by simp [mul_comm]
end GroundTheory.LocalField
