-- Prove2me | solution 1 for GroundTheory.LocalField.character_leftRegular_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:09.134681+00:00
-- url     : https://prove2.me/submissions/63d987f9-60cb-4419-94fa-9b230085b26c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_character_eq_sum_irrChars
import Theorems.Thm_GroundTheory_LocalField_charInner_leftRegular

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
theorem _root_.solution :
    (Representation.leftRegular ℂ G).character = ∑ ψ ∈ irrChars G, ψ 1 • ψ := by
  conv_lhs => rw [character_eq_sum_irrChars (Representation.leftRegular ℂ G)]
  simp_rw [charInner_leftRegular]
end GroundTheory.LocalField
