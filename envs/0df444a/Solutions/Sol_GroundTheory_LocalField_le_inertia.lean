-- Prove2me | solution 1 for GroundTheory.LocalField.le_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:09.845952+00:00
-- url     : https://prove2.me/submissions/8ddf7dd6-154e-4981-91e0-394bf6cd3396

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionClifford

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
variable {G : Type*} [Group G] (A : Subgroup G) [hA : A.Normal]
namespace GroundTheory.LocalField
theorem _root_.solution {θ : A → ℂ} (hθ : IsClassFun θ) : A ≤ inertia A θ := by
  intro x hx a
  have := hθ a ⟨x, hx⟩⁻¹
  convert this using 2
  ext
  simp
end GroundTheory.LocalField
