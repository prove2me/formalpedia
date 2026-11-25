-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.perm_eq_of_llRank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:47.783809+00:00
-- url     : https://prove2.me/submissions/b9b4f793-e51a-41a2-b269-04742dde7acd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_llRank_permGL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_card_filter_le_eq
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_card_filter_lt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {w w' : Equiv.Perm (Fin n)}
    (h : ∀ i j, llRank i j (permGL F w) = llRank i j (permGL F w')) : w = w' := by
  have key : ∀ r j, (w⁻¹ r ≤ j ↔ w'⁻¹ r ≤ j) := by
    intro r j
    have hA : (Finset.univ.filter fun x : Fin n => r ≤ x ∧ w⁻¹ x ≤ j).card =
        (Finset.univ.filter fun x : Fin n => r ≤ x ∧ w'⁻¹ x ≤ j).card := by
      rw [← llRank_permGL (F := F), ← llRank_permGL (F := F), h]
    have hB : (Finset.univ.filter fun x : Fin n => r < x ∧ w⁻¹ x ≤ j).card =
        (Finset.univ.filter fun x : Fin n => r < x ∧ w'⁻¹ x ≤ j).card := by
      rw [card_filter_lt_eq (F := F), card_filter_lt_eq (F := F)]
      split_ifs with hr
      · exact h _ _
      · rfl
    have e1 := card_filter_le_eq w r j
    rw [hA, card_filter_le_eq w' r j, hB] at e1
    constructor
    · intro hw
      by_contra hw'
      rw [if_pos hw, if_neg hw'] at e1
      omega
    · intro hw'
      by_contra hw
      rw [if_pos hw', if_neg hw] at e1
      omega
  have hinv : w⁻¹ = w'⁻¹ := by
    ext r
    exact congrArg Fin.val (le_antisymm ((key r (w'⁻¹ r)).2 le_rfl) ((key r (w⁻¹ r)).1 le_rfl))
  exact inv_injective hinv
end GroundTheory.Automorphic.Whittaker
