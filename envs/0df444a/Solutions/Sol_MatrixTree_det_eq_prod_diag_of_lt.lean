-- Prove2me | solution 1 for MatrixTree.det_eq_prod_diag_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:07:09.607841+00:00
-- url     : https://prove2.me/submissions/2002e88a-0b06-4c6e-90b5-bcee24d5f4f2

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (b : ι → ℕ) (h : ∀ i j, M i j ≠ 0 → i = j ∨ b i < b j) :
    M.det = ∏ i, M i i := by
  rw [det_apply', Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    by_contra hne
    have hall : ∀ i, M (σ i) i ≠ 0 := fun i hi =>
      hne (by rw [Finset.prod_eq_zero (f := fun j => M (σ j) j) (mem_univ i) hi, mul_zero])
    have hle : ∀ i, b (σ i) ≤ b i := fun i =>
      (h _ _ (hall i)).elim (fun e => by rw [e]) le_of_lt
    obtain ⟨i0, hi0⟩ : ∃ i, σ i ≠ i := by
      by_contra hc; push Not at hc; exact hσ (Equiv.ext hc)
    have hlt : b (σ i0) < b i0 := (h _ _ (hall i0)).resolve_left hi0
    have : ∑ i, b (σ i) < ∑ i, b i := Finset.sum_lt_sum (fun i _ => hle i) ⟨i0, mem_univ _, hlt⟩
    rw [Equiv.sum_comp σ b] at this
    exact lt_irrefl _ this
  · simp
end MatrixTree
