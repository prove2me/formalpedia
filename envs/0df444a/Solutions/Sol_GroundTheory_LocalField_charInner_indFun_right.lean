-- Prove2me | solution 1 for GroundTheory.LocalField.charInner_indFun_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:46.389864+00:00
-- url     : https://prove2.me/submissions/e3ffc4bc-eb28-4d59-8272-8ba113dfb3d8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Theorems.Thm_GroundTheory_LocalField_charInner_comm


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
theorem _root_.solution (φ : H →* G) (ψ : H → ℂ) {χ : G → ℂ} (hχ : IsClassFun χ) :
    charInner G χ (indFun φ ψ) = charInner H (χ ∘ φ) ψ := by
  rw [charInner_comm, charInner_indFun φ ψ hχ, charInner_comm]
end GroundTheory.LocalField
