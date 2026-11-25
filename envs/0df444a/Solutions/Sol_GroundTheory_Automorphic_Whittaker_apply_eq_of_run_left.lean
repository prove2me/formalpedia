-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.apply_eq_of_run_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:26.362831+00:00
-- url     : https://prove2.me/submissions/59e24ae1-c65c-4fdf-bcca-40cb52d82d00

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_add_eq_of_le_left

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
    ∀ k : ℕ, ∀ x : Fin n, x.val + k = b.val →
      k ≤ #(univ.filter fun y : Fin n => y < b ∧ w y < w b) → t (w x) = t (w b) := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    have : x = b := Fin.ext (by omega)
    rw [this]
  | succ k ih =>
    intro x hx hk
    have hbn := b.isLt
    have hx1 : x.val + 1 < n := by omega
    have h1 := ih ⟨x.val + 1, hx1⟩ (by simp; omega) (by omega)
    have e1 := val_add_eq_of_le_left hB b x (Fin.le_iff_val_le_val.2 (by omega)) (by omega)
    have e2 := val_add_eq_of_le_left hB b ⟨x.val + 1, hx1⟩ (Fin.le_iff_val_le_val.2 (by simp; omega))
      (by simp; omega)
    have hasc : w x < w ⟨x.val + 1, hx1⟩ := by
      rw [Fin.lt_def]
      simp only at e2
      omega
    have := ht x hx1 hasc
    rw [this]
    exact h1
end GroundTheory.Automorphic.Whittaker
