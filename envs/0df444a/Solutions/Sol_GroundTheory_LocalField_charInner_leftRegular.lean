-- Prove2me | solution 1 for GroundTheory.LocalField.charInner_leftRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:32.043873+00:00
-- url     : https://prove2.me/submissions/903d82b0-7541-488f-828e-b2efcc4507aa

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_character_leftRegular_apply

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
theorem _root_.solution (ψ : G → ℂ) :
    charInner G (Representation.leftRegular ℂ G).character ψ = ψ 1 := by
  classical
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [charInner_apply]
  simp_rw [character_leftRegular_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), inv_one, Nat.card_eq_fintype_card, ← mul_assoc,
    inv_mul_cancel₀ hG, one_mul]
end GroundTheory.LocalField
