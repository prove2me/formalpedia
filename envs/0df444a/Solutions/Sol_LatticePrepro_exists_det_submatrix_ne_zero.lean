-- Prove2me | solution 1 for LatticePrepro.exists_det_submatrix_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:27:55.416113+00:00
-- url     : https://prove2.me/submissions/825550ea-bd84-4ae3-b348-a80ec5814a06

import Mathlib


namespace LatticePrepro

open Polynomial Matrix

section Minor

variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

/-- From a matrix of rank `k` one can pick `k` linearly independent columns. -/
theorem exists_linearIndependent_cols (A : Matrix m n K) {k : ℕ} (hk : A.rank = k) :
    ∃ c : Fin k → n, LinearIndependent K (fun j => A.col (c j)) := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range A.col)
  have hbfin : b.Finite := (Set.finite_range A.col).subset hb
  have : Fintype b := hbfin.fintype
  have hcard : Fintype.card b = k := by
    have h1 := finrank_span_eq_card (R := K) hli
    rw [Subtype.range_coe, hspan, ← Matrix.rank_eq_finrank_span_cols, hk] at h1
    exact h1.symm
  let e : Fin k ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hchoice : ∀ x : b, ∃ j, A.col j = x := fun x => hb x.2
  choose c hc using hchoice
  refine ⟨fun j => c (e j), ?_⟩
  have : (fun j => A.col (c (e j))) = fun j => ((e j : b) : m → K) := by
    funext j; exact hc (e j)
  rw [this]
  exact hli.comp e e.injective

/-- A matrix with linearly independent columns has rank equal to its number of columns. -/
theorem rank_eq_card_of_linearIndependent_cols (A : Matrix m n K)
    (h : LinearIndependent K A.col) : A.rank = Fintype.card n := by
  rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card h]

/-- A matrix of rank `k` has a nonzero `k × k` minor. -/
private theorem exists_det_submatrix_ne_zero [Fintype m] (A : Matrix m n K) {k : ℕ} (hk : A.rank = k) :
    ∃ (r : Fin k → m) (c : Fin k → n), (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_linearIndependent_cols A hk
  set N : Matrix m (Fin k) K := A.submatrix id c with hN
  have hNcol : N.col = fun j => A.col (c j) := by
    funext j; ext i; rfl
  have hNrank : N.rank = k := by
    rw [rank_eq_card_of_linearIndependent_cols N (hNcol ▸ hc), Fintype.card_fin]
  have hNt : Nᵀ.rank = k := by rw [Matrix.rank_transpose, hNrank]
  obtain ⟨r, hr⟩ := exists_linearIndependent_cols Nᵀ hNt
  refine ⟨r, c, ?_⟩
  have hrows : LinearIndependent K (A.submatrix r c).row := by
    have : (A.submatrix r c).row = fun i => Nᵀ.col (r i) := by
      funext i; ext j; rfl
    rw [this]; exact hr
  have hunit : IsUnit (A.submatrix r c) := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end Minor

end LatticePrepro

open Polynomial Matrix
variable {K : Type*} [Field K] {m n : Type*} [Fintype n]
theorem solution [Fintype m] (A : Matrix m n K) {k : ℕ} (hk : A.rank = k) :
    ∃ (r : Fin k → m) (c : Fin k → n), (A.submatrix r c).det ≠ 0 :=
  @LatticePrepro.exists_det_submatrix_ne_zero K _ m n _ _ A k hk
