-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:44:18.195618+00:00
-- url     : https://prove2.me/submissions/13487a9c-71e0-4ad7-b85e-23ceba6b9491

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_antidiag_fin_reindex_generic

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℕ → ℂ) (k : ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k,
      ∏ i, w i (l i)) =
    ∑ f : ι → Fin (k + 1),
      if (∑ i, (f i).val) = k then
        ∏ i, w i (f i).val
      else 0 := by
  simpa using
    (OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_generic
      (fun x : ι → ℕ => ∏ i, w i (x i)) k)
