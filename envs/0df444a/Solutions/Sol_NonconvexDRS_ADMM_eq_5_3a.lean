-- Prove2me | solution 1 for NonconvexDRS.ADMM.eq_5_3a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:48:38.29609+00:00
-- url     : https://prove2.me/submissions/58b55662-c2f7-40d5-a02f-7f9ed92e6763

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

theorem solution {m p : ℕ} (f : EuclideanSpace ℝ (Fin m) → EReal)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (γ : ℝ) (hγ : 0 < γ) (s : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ x', f x + ((‖A x - s‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
      f x' + ((‖A x' - s‖ ^ 2 / (2 * γ) : ℝ) : EReal)) :
    A x ∈ NonconvexDRS.Tight.proxSet (imageFn A f) γ s := by
  intro w'
  have hup : imageFn A f (A x) ≤ f x := by
    unfold imageFn
    exact iInf₂_le (f := fun x' (_ : A x' = A x) => f x') x rfl
  have h0 : imageFn A f (A x) + ((‖A x - s‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≤
      f x + ((‖A x - s‖ ^ 2 / (2 * γ) : ℝ) : EReal) := add_le_add hup le_rfl
  apply jj_le_add
  unfold imageFn at h0 ⊢
  apply le_iInf₂
  intro x' hx'
  have h1 := hx x'
  rw [hx'] at h1
  have h2 := add_le_add (h0.trans h1) (le_refl (((-(‖w' - s‖ ^ 2 / (2 * γ)) : ℝ)) : EReal))
  rwa [jj_cancel] at h2
