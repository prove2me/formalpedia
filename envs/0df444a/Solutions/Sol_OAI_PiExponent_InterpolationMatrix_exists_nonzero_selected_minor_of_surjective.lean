-- Prove2me | solution 1 for OAI.PiExponent.InterpolationMatrix.exists_nonzero_selected_minor_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:27:11.611772+00:00
-- url     : https://prove2.me/submissions/99887e42-4413-4db1-9b09-a5fdc30c0b27

import Mathlib

open scoped BigOperators

namespace PXCol

theorem cols {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix α β ℂ) (hM : Function.Surjective M.mulVecLin) :
    ∃ f : α → β, Function.Injective f ∧ LinearIndependent ℂ (fun i => M.col (f i)) := by
  classical
  set s : Set (α → ℂ) := Set.range M.col with hs
  have hspan : Submodule.span ℂ s = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, rfl⟩ := hM v
    have : M.mulVecLin c = ∑ b, c b • M.col b := by
      ext a
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ (fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
  obtain ⟨t, hts, htspan, hli⟩ := exists_linearIndependent ℂ s
  rw [hspan] at htspan
  have htfin : t.Finite := (Set.finite_range _).subset hts
  haveI : Fintype t := htfin.fintype
  have hcard : Fintype.card t = Fintype.card α := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.mp hli
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, Set.finrank, htspan, finrank_top,
      Module.finrank_fintype_fun_eq_card] at h1
    exact h1
  have hg : ∀ x : t, ∃ b : β, M.col b = x := fun x => hts x.2
  choose g hg using hg
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    rw [← hg x, ← hg y, hxy]
  let e : α ≃ t := Fintype.equivOfCardEq hcard.symm
  refine ⟨g ∘ e, hginj.comp e.injective, ?_⟩
  have : (fun i => M.col ((g ∘ e) i)) = (fun x : t => (x : α → ℂ)) ∘ e := by
    funext i; simp [hg]
  rw [this]
  exact hli.comp e e.injective

end PXCol

theorem solution
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : Matrix α β Complex) (hM : Function.Surjective M.mulVecLin) :
    ∃ f : α → β, Function.Injective f ∧ (M.submatrix id f).det ≠ 0 := by
  obtain ⟨f, hf, hli⟩ := PXCol.cols M hM
  refine ⟨f, hf, ?_⟩
  have hu : IsUnit (M.submatrix id f) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have : (M.submatrix id f).col = fun i => M.col (f i) := by
      funext i a; simp [Matrix.col, Matrix.submatrix]
    rw [this]; exact hli
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
  exact hu
