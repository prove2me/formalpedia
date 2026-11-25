-- Prove2me | solution 1 for GroundTheory.LocalField.sum_irrChars_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:54.899799+00:00
-- url     : https://prove2.me/submissions/a06132f8-be8b-417b-a195-fb3ebd70729c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionCharacters
import Theorems.Thm_GroundTheory_LocalField_character_leftRegular_apply
import Theorems.Thm_GroundTheory_LocalField_character_leftRegular_eq_sum

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
theorem _root_.solution [DecidableEq G] (g : G) :
    ∑ ψ ∈ irrChars G, ψ 1 * ψ g = if g = 1 then (Nat.card G : ℂ) else 0 := by
  have h := congrFun (character_leftRegular_eq_sum (G := G)) g
  rw [character_leftRegular_apply, Finset.sum_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [← h, Nat.card_eq_fintype_card]
end GroundTheory.LocalField
