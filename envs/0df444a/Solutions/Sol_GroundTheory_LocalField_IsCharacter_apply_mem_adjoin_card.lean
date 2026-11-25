-- Prove2me | solution 1 for GroundTheory.LocalField.IsCharacter.apply_mem_adjoin_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:17.379803+00:00
-- url     : https://prove2.me/submissions/e91ee614-dab5-469a-a8e3-20fda834cbe4

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Theorems.Thm_GroundTheory_LocalField_IsCharacter_apply_mem_adjoin

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
namespace IsCharacter
theorem _root_.solution {χ : G → ℂ} (hχ : IsCharacter χ) (s : G) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Nat.card G)) : χ s ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  exact hχ.apply_mem_adjoin s hζ (orderOf_dvd_natCard s)
end IsCharacter
end GroundTheory.LocalField
