-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_subtype
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:03:59.097614+00:00
-- url     : https://prove2.me/submissions/8c90483f-3b90-4bfc-be6e-000d381414bf

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_antidiag_fin_reindex_equiv

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → ℕ) → ℂ) (k : ℕ) :
    (∑ l : {l : ι →₀ ℕ // l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k}, φ l.1) =
    ∑ f : {f : ι → Fin (k + 1) // (∑ i, (f i).val) = k},
      φ (fun i => (f.1 i).val) := by
  classical
  obtain ⟨e, he⟩ :=
    OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_equiv
      (ι := ι) k
  apply Fintype.sum_equiv e
  intro l
  congr 1
  funext i
  exact (he l i).symm
