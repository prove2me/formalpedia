-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_generic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:54:12.745814+00:00
-- url     : https://prove2.me/submissions/3a0bd4c2-22fc-48fc-87f1-121223ea8f90

import Mathlib.Tactic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Theorems.Thm_OAI_PiExponent_MatrixTranslationBounds_coeff_prod_antidiag_fin_reindex_subtype

open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → ℕ) → ℂ) (k : ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k, φ l) =
    ∑ f : ι → Fin (k + 1),
      if (∑ i, (f i).val) = k then
        φ (fun i => (f i).val)
      else 0 := by
  classical
  calc
    _ = ∑ l : {l : ι →₀ ℕ //
          l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) k}, φ l.1 := by
      exact Finset.sum_subtype _ (fun _ => Iff.rfl)
        (fun l : ι →₀ ℕ => φ l)
    _ = ∑ f : {f : ι → Fin (k + 1) // (∑ i, (f i).val) = k},
          φ (fun i => (f.1 i).val) :=
      OAI.PiExponent.MatrixTranslationBounds.coeff_prod_antidiag_fin_reindex_subtype φ k
    _ = ∑ f ∈ Finset.univ.filter
          (fun f : ι → Fin (k + 1) => (∑ i, (f i).val) = k),
          φ (fun i => (f i).val) := by
      exact (Finset.sum_subtype
        (p := fun f : ι → Fin (k + 1) => (∑ i, (f i).val) = k)
        (Finset.univ.filter
          (fun f : ι → Fin (k + 1) => (∑ i, (f i).val) = k))
        (fun f => by simp)
        (fun f : ι → Fin (k + 1) => φ (fun i => (f i).val))).symm
    _ = _ := by rw [Finset.sum_filter]