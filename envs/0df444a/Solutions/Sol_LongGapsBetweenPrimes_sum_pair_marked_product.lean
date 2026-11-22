-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_pair_marked_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:08.599957+00:00
-- url     : https://prove2.me/submissions/b3fd8cf1-eca2-44e3-988b-5396e4af2b99

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (w : Ω → ℝ) (hw : ∑ d, w d = 1)
    (mark : Ω → Prop) [DecidablePred mark] (i j : ι) (hij : i ≠ j) :
    (∑ r : ι → Ω, (∏ ℓ, w (r ℓ)) * if mark (r i) ∧ mark (r j) then 1 else 0) =
      (∑ d, w d * if mark d then 1 else 0) ^ 2 := by
  classical
  calc
    _ = ∏ ℓ, ∑ d, w d * if (ℓ = i ∨ ℓ = j) → mark d then 1 else 0 := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.prod_mul_distrib, Finset.prod_boole]
      congr 1
      simp only [Finset.mem_univ, forall_true_left, or_imp, forall_and, forall_eq]
    _ = ∏ ℓ ∈ ({i, j} : Finset ι), ∑ d, w d * if mark d then 1 else 0 := by
      rw [← Finset.prod_subset (Finset.subset_univ ({i, j} : Finset ι))]
      · simp [hij, Finset.prod_pair hij]
      · intro ℓ _ hℓ
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hℓ
        simp [hℓ.1, hℓ.2, hw]
    _ = _ := by simp [Finset.prod_pair hij, pow_two]
end LongGapsBetweenPrimes
