-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.apply_eq_of_run_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:27.114801+00:00
-- url     : https://prove2.me/submissions/0957bd26-4d9f-4535-8994-20152301f641

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_eq_of_le_right

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
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val = b.val + k →
      k ≤ #(univ.filter fun y : Fin n => b < y ∧ w b < w y) → t (w x) = t (w b) := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    have : x = b := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    intro x hx hk
    have hxn := x.isLt
    have hk1 : b.val + k < n := by omega
    have h1 := ih ⟨b.val + k, hk1⟩ rfl (by omega)
    have e1 := val_eq_of_le_right hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    have e2 := val_eq_of_le_right hB b ⟨b.val + k, hk1⟩ (Fin.le_iff_val_le_val.2 (by simp))
      (by simp; omega)
    have hk2 : b.val + k + 1 < n := by omega
    have hnext : (⟨b.val + k + 1, hk2⟩ : Fin n) = x := Fin.ext (by simp; omega)
    have hasc : w ⟨b.val + k, hk1⟩ < w ⟨b.val + k + 1, hk2⟩ := by
      rw [hnext, Fin.lt_def]
      simp only at e2
      omega
    have := ht ⟨b.val + k, hk1⟩ hk2 hasc
    simp only at this
    rw [hnext] at this
    rw [← this, h1]
end GroundTheory.Automorphic.Whittaker
