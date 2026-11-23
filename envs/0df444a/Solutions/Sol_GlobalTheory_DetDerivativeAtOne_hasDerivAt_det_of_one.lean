-- Prove2me | solution 1 for GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:34.394281+00:00
-- url     : https://prove2.me/submissions/7e4669f6-c34f-46ed-b128-cba7d05b8673

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasDerivAtDetOfOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DetDerivativeAtOne
open Equiv Finset
namespace GlobalTheory.DetDerivativeAtOne
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A (0 : ℝ) = (1 : Matrix n n ℂ))
    (hd : ∀ (i j : n), HasDerivAt (fun (t : ℝ) ↦ A t i j) (A' i j) (0 : ℝ)) :
    HasDerivAt (fun (t : ℝ) ↦ Matrix.det (A t)) (Matrix.trace A') (0 : ℝ) := by
  have hfun : (fun t : ℝ ↦ Matrix.det (A t)) =
      fun t ↦ ∑ σ : Perm n, ((Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i :=
    funext fun t ↦ Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ : Perm n, HasDerivAt (fun t : ℝ ↦ ∏ i, A t (σ i) i)
      (∑ i, (∏ j ∈ univ.erase i, A 0 (σ j) j) • A' (σ i) i) 0 :=
    fun σ ↦ HasDerivAt.fun_finsetProd (fun i _ ↦ hd (σ i) i)
  have hsum := HasDerivAt.fun_sum (u := (univ : Finset (Perm n)))
    (fun σ _ ↦ (hσ σ).const_mul ((Perm.sign σ : ℤ) : ℂ))
  refine hsum.congr_deriv (Eq.symm ?_)
  rw [h0]
  rw [Finset.sum_eq_single (1 : Perm n)]
  · simp [Matrix.trace, Perm.one_apply, Matrix.one_apply]
  · intro σ _ hσ1
    have hz : ∀ i, (∏ j ∈ univ.erase i, (1 : Matrix n n ℂ) (σ j) j) = 0 := by
      intro i
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hc
        push Not at hc
        exact hσ1 (Equiv.ext hc)
      by_cases hki : k = i
      · subst hki
        apply Finset.prod_eq_zero (i := σ k)
        · simp [hk]
        · have : σ (σ k) ≠ σ k := fun h ↦ hk (σ.injective h)
          simp [Matrix.one_apply_ne this]
      · apply Finset.prod_eq_zero (i := k)
        · simp [hki]
        · simp [Matrix.one_apply_ne hk]
    simp [hz]
  · intro h; exact absurd (Finset.mem_univ _) h
end GlobalTheory.DetDerivativeAtOne
