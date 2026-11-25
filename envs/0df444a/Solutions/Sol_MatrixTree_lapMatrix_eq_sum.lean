-- Prove2me | solution 1 for MatrixTree.lapMatrix_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:30:48.610114+00:00
-- url     : https://prove2.me/submissions/6f1ad969-4853-428d-88a8-5d8c8b37ef23

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree
public import Theorems.Thm_MatrixTree_inc_of_not_mem
public import Theorems.Thm_MatrixTree_inc_mul_self
public import Theorems.Thm_MatrixTree_inc_mul_inc_of_ne

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
namespace MatrixTree
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) :
    G.lapMatrix ℤ x y = ∑ e ∈ G.edgeFinset, inc e x * inc e y := by
  simp only [lapMatrix, degMatrix, Matrix.sub_apply, adjMatrix_apply, diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [Finset.sum_congr rfl fun e he => inc_mul_self (G.not_isDiag_of_mem_edgeSet
      (mem_edgeFinset.mp he)) x, Finset.sum_boole, ← incidenceFinset_eq_filter,
      card_incidenceFinset_eq_degree]
    simp
  · have hzero : ∀ e, e ≠ s(x, y) → inc e x * inc e y = 0 := by
      intro e hne
      by_cases hx : x ∈ e
      · have hy : y ∉ e := fun hy => hne ((Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩)
        rw [inc_of_not_mem hy, mul_zero]
      · rw [inc_of_not_mem hx, zero_mul]
    by_cases hadj : G.Adj x y
    · rw [Finset.sum_eq_single s(x, y) (fun e _ hne => hzero e hne)
        (fun h => absurd (mem_edgeFinset.mpr hadj) h),
        inc_mul_inc_of_ne (G.not_isDiag_of_mem_edgeSet hadj) hxy (Sym2.mem_mk_left _ _)
          (Sym2.mem_mk_right _ _)]
      simp [hxy, hadj]
    · rw [Finset.sum_eq_zero fun e he => hzero e (by
        rintro rfl; exact hadj (mem_edgeFinset.mp he))]
      simp [hxy, hadj]
end MatrixTree
