-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.relevant_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:18.28829+00:00
-- url     : https://prove2.me/submissions/d9891dcf-4371-46fd-8544-e313529de44c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_eq_of_le_right
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_add_eq_of_le_left
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_add_card_right

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
theorem _root_.solution
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b : Fin n) :
    w (Fin.rev (w b)) = Fin.rev b := by
  have hid := val_add_card_right w b
  set r := #(univ.filter fun y : Fin n => b < y ∧ w b < w y)
  set l := #(univ.filter fun y : Fin n => y < b ∧ w y < w b)
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  have hwb := (w b).isLt
  apply Fin.ext
  rw [Fin.val_rev]
  by_cases hcb : b.val ≤ c.val
  · have := val_eq_of_le_right hB b c (Fin.le_iff_val_le_val.2 hcb) (by omega)
    omega
  · have := val_add_eq_of_le_left hB b c (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    omega
end GroundTheory.Automorphic.Whittaker
