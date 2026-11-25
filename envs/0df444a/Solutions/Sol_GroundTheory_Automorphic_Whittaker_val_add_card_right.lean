-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.val_add_card_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:39.725894+00:00
-- url     : https://prove2.me/submissions/f11c9fd1-a0bd-43e7-8cad-b4263a07741a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_card_filter_lt_apply

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
open Finset
variable {n : ℕ} {w : Equiv.Perm (Fin n)}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (w : Equiv.Perm (Fin n)) (b : Fin n) :
    (w b).val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y) =
      #(univ.filter fun y : Fin n => y < b ∧ w y < w b) + (n - 1 - b.val) := by
  have hIoi : #(univ.filter fun y : Fin n => b < y) = n - 1 - b.val := by
    have : (univ.filter fun y : Fin n => b < y) = Ioi b := by
      ext y
      simp
    rw [this, Fin.card_Ioi]
  rw [← card_filter_lt_apply w b, ← hIoi, card_filter, card_filter, card_filter, card_filter,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  have hne : y ≠ b → w y ≠ w b := fun h e => h (w.injective e)
  rcases lt_trichotomy y b with h | h | h
  · have h' : ¬ b < y := not_lt.2 (le_of_lt h)
    by_cases hw : w y < w b <;> simp [h, h', hw]
  · subst h
    simp
  · have h' : ¬ y < b := not_lt.2 (le_of_lt h)
    have hyb : w y ≠ w b := hne (ne_of_gt h)
    rcases lt_or_gt_of_ne hyb with hw | hw
    · have hw' : ¬ w b < w y := not_lt.2 (le_of_lt hw)
      simp [h, h', hw, hw']
    · have hw' : ¬ w y < w b := not_lt.2 (le_of_lt hw)
      simp [h, h', hw, hw']
end GroundTheory.Automorphic.Whittaker
