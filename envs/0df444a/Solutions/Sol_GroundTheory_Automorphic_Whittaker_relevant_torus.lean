-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.relevant_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:17.247046+00:00
-- url     : https://prove2.me/submissions/c04ff35b-20ed-494e-ae30-a7a015f9553f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_add_card_right
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_relevant_involution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_apply_eq_of_run_right
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_apply_eq_of_run_left

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
theorem _root_.solution {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) : t (w b) = t (Fin.rev b) := by
  have hid := val_add_card_right w b
  rw [← relevant_involution hB b]
  set c := Fin.rev (w b) with hc
  have hcv : c.val = n - (↑(w b) + 1) := by rw [hc, Fin.val_rev]
  have hb := b.isLt
  have hwb := (w b).isLt
  by_cases hcb : b.val ≤ c.val
  · exact (apply_eq_of_run_right t hB ht b (c.val - b.val) c (by omega) (by omega)).symm
  · exact (apply_eq_of_run_left t hB ht b (b.val - c.val) c (by omega) (by omega)).symm
end GroundTheory.Automorphic.Whittaker
