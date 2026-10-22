-- Prove2me | solution 1 for NonconvexDRS.ADMM.prop_5_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:46:50.498354+00:00
-- url     : https://prove2.me/submissions/6f3b0bec-bac8-4792-ab92-202527750d1c

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

theorem solution {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (β : ℝ) (hβ : 0 < β) (s : EuclideanSpace ℝ (Fin p))
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
