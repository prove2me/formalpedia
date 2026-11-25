-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.character_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:12.086898+00:00
-- url     : https://prove2.me/submissions/89269156-4acd-4f7e-99fe-9a293369b4a8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Theorems.Thm_GroundTheory_Global_Cyclotomic_pow_val_one
import Theorems.Thm_GroundTheory_Global_Cyclotomic_character_spec
import Theorems.Thm_GroundTheory_Global_Cyclotomic_eq_character

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
open scoped Pointwise
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (σ : Gal(ℚ̄/ℚ)) :
    character σ = 1 ↔ ∀ x : ℚ̄, (∃ n : ℕ, 0 < n ∧ x ^ n = 1) → σ x = x := by
  constructor
  · rintro h x ⟨n, hn, hx⟩
    obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, hn⟩, rfl⟩
    have := character_spec σ N hx
    rw [h, Units.val_one, map_one, pow_val_one hx] at this
    exact this
  · intro h
    refine Units.ext (eq_character σ 1 fun n t ht => ?_).symm
    rw [map_one, pow_val_one ht]
    exact h t ⟨n, n.pos, ht⟩
end GroundTheory.Global.Cyclotomic
