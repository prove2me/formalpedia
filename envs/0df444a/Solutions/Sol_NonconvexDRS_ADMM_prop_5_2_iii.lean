-- Prove2me | solution 1 for NonconvexDRS.ADMM.prop_5_2_iii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:46:56.636674+00:00
-- url     : https://prove2.me/submissions/4ccf1242-0814-448e-93d2-edcb69b29375

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

lemma jj_le_of_add_le (a b : EReal) (r : ℝ) (h : a + (r : EReal) ≤ b + (r : EReal)) : a ≤ b := by
  have := add_le_add h (le_refl (((-r : ℝ)) : EReal))
  rwa [jj_cancel, jj_cancel] at this

lemma jj_le_add (A F : EReal) (c : ℝ) (h : A + ((-c : ℝ) : EReal) ≤ F) : A ≤ F + (c : EReal) := by
  have h2 := add_le_add h (le_refl (c : EReal))
  have h3 := jj_cancel A (-c)
  rw [neg_neg] at h3
  rwa [h3] at h2

lemma jj_ii {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (β : ℝ) (s : EuclideanSpace ℝ (Fin p))
    (xβ : EuclideanSpace ℝ (Fin n)) (hxβ : xβ ∈ Xbeta h C β s) :
    imageFn C h (C xβ) = h xβ := by
  unfold imageFn
  apply le_antisymm
  · exact iInf₂_le (f := fun x (_ : C x = C xβ) => h x) xβ rfl
  · apply le_iInf₂
    intro x' hx'
    have := hxβ x'
    rw [hx'] at this
    exact jj_le_of_add_le _ _ _ this

theorem solution {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (β : ℝ) (hβ : 0 < β) (s : EuclideanSpace ℝ (Fin p))
    (xβ : EuclideanSpace ℝ (Fin n)) (hxβ : xβ ∈ Xbeta h C β s) :
    C xβ ∈ NonconvexDRS.Tight.proxSet (imageFn C h) (1 / β) s := by
  have e : ∀ v : EuclideanSpace ℝ (Fin p), ‖v - s‖ ^ 2 / (2 * (1 / β)) = β / 2 * ‖v - s‖ ^ 2 := by
    intro v
    field_simp
  intro w'
  simp only [e]
  rw [jj_ii h C β s xβ hxβ]
  apply jj_le_add
  unfold imageFn
  apply le_iInf₂
  intro x hx
  have h1 := hxβ x
  rw [hx] at h1
  have h2 := add_le_add h1 (le_refl (((-(β / 2 * ‖w' - s‖ ^ 2) : ℝ)) : EReal))
  rwa [jj_cancel] at h2
