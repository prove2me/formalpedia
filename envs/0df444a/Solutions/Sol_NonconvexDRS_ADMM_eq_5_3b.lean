-- Prove2me | solution 1 for NonconvexDRS.ADMM.eq_5_3b
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:48:46.543562+00:00
-- url     : https://prove2.me/submissions/2063f26f-f5c9-4bb6-8360-f56a5b85da7f

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting
set_option autoImplicit false
open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace
open NonconvexDRS.ADMM

lemma jj_cancel (a : EReal) (r : ℝ) : a + (r : EReal) + ((-r : ℝ) : EReal) = a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_add, ← EReal.coe_add]
    congr 1
    ring

lemma jj_le_add (A F : EReal) (c : ℝ) (h : A + ((-c : ℝ) : EReal) ≤ F) : A ≤ F + (c : EReal) := by
  have h2 := add_le_add h (le_refl (c : EReal))
  have h3 := jj_cancel A (-c)
  rw [neg_neg] at h3
  rwa [h3] at h2

theorem solution {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (b : EuclideanSpace ℝ (Fin p))
    (γ : ℝ) (hγ : 0 < γ) (s : EuclideanSpace ℝ (Fin p)) (z : EuclideanSpace ℝ (Fin n))
    (hz : ∀ z', g z + ((‖B z + s - b‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
      g z' + ((‖B z' + s - b‖ ^ 2 / (2 * γ) : ℝ) : EReal)) :
    b - B z ∈ NonconvexDRS.Tight.proxSet (fun t => imageFn B g (b - t)) γ s := by
  intro w'
  have hn : ‖(b - B z) - s‖ = ‖B z + s - b‖ := by
    rw [← norm_neg]; congr 1; abel
  have hup : imageFn B g (b - (b - B z)) ≤ g z := by
    rw [sub_sub_cancel]
    unfold imageFn
    exact iInf₂_le (f := fun z' (_ : B z' = B z) => g z') z rfl
  have h0 : imageFn B g (b - (b - B z)) + ((‖B z + s - b‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
      g z + ((‖B z + s - b‖ ^ 2 / (2 * γ) : ℝ) : EReal) := add_le_add hup le_rfl
  show imageFn B g (b - (b - B z)) + ((‖(b - B z) - s‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
    imageFn B g (b - w') + ((‖w' - s‖ ^ 2 / (2 * γ) : ℝ) : EReal)
  rw [hn]
  apply jj_le_add
  unfold imageFn
  apply le_iInf₂
  intro z' hz'
  have h1 := hz z'
  have hn2 : ‖B z' + s - b‖ = ‖w' - s‖ := by
    rw [hz', norm_sub_rev (w' : EuclideanSpace ℝ (Fin p)) s]
    congr 1; abel
  rw [hn2] at h1
  have h2 := add_le_add (h0.trans h1) (le_refl (((-(‖w' - s‖ ^ 2 / (2 * γ)) : ℝ)) : EReal))
  rw [jj_cancel] at h2
  exact h2
