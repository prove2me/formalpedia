-- Prove2me | solution 1 for GroundTheory.LocalField.IsElementary.exists_eq_indLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:46:43.645828+00:00
-- url     : https://prove2.me/submissions/43fa4ae3-8a91-4b98-a0c0-47a6fa70a09a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionAssembly
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionMonomial
import Definitions.Def_GroundTheory_LocalFields_BrauerInduction
import Theorems.Thm_GroundTheory_LocalField_IsElementaryAt_isNilpotent
import Theorems.Thm_GroundTheory_LocalField_IsIrrCharacter_exists_eq_indFun_of_isNilpotent


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
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace GroundTheory.LocalField
namespace IsElementary
theorem _root_.solution {K : Subgroup G} (hK : IsElementary K) {χ : K → ℂ}
    (hχ : IsIrrCharacter χ) : ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ := by
  obtain ⟨p, hp, hKp⟩ := hK
  have := hKp.isNilpotent hp
  obtain ⟨L, μ, h⟩ := hχ.exists_eq_indFun_of_isNilpotent
  exact ⟨L, μ, by rw [h, indLin]⟩
end IsElementary
end GroundTheory.LocalField
