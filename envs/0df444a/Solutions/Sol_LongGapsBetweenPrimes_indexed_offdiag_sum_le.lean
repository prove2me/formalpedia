-- Prove2me | solution 1 for LongGapsBetweenPrimes.indexed_offdiag_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:35.092794+00:00
-- url     : https://prove2.me/submissions/c617c823-efc7-4be0-b7ee-6b6323d94f3d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {ι Λ : Type*} [Fintype ι] [Fintype Λ]
    [DecidableEq ι] (σ : ι → Λ) (hσ : Function.Injective σ)
    (K : Λ → Λ → ℝ) (hdiag : ∀ j, K j j = 1) (i : ι) :
    (∑ j : ι, if j = i then 0 else |K (σ i) (σ j)|) ≤
      (∑ τ : Λ, |K (σ i) τ|) - 1 := by
  classical
  rw [le_sub_iff_add_le]
  calc
    _ = ∑ j : ι, |K (σ i) (σ j)| := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp [hdiag, Finset.sum_ite, Finset.filter_ne']
    _ = ∑ τ ∈ Finset.univ.image σ, |K (σ i) τ| := by
      rw [Finset.sum_image hσ.injOn]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun τ _ _ => abs_nonneg (K (σ i) τ))
end LongGapsBetweenPrimes
