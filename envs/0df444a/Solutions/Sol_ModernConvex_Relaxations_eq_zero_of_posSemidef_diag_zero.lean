-- Prove2me | solution 1 for ModernConvex.Relaxations.eq_zero_of_posSemidef_diag_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:39.24701+00:00
-- url     : https://prove2.me/submissions/a947f16e-3f92-452f-afe3-b6447041fa58

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

/-!
# Base cases of the rational PSD oracle

The rational oracle decides `M ⪰ 0` for a symmetric rational `M` by symmetric elimination: it
either produces a proof of semidefiniteness or a rational `v` with `vᵀMv < 0`. Two branches of
that recursion are closed here, and they are the ones that make the recursion terminate:

* **negative diagonal**: if `M i i < 0` then `eᵢᵀ M eᵢ = M i i < 0`, so `v = eᵢ` certifies;
* **zero diagonal**: a positive semidefinite matrix with zero diagonal is **zero** (its `2×2`
  principal minors have nonnegative determinant `−M_ij²`), so if all diagonal entries vanish and
  `M ≠ 0`, some off-diagonal entry is nonzero and a two-point vector certifies.

Both certificates are built from entries of `M` by signs and comparisons, hence are rational
whenever `M` is.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **A positive semidefinite matrix with zero diagonal is zero.** -/
theorem eq_zero_of_posSemidef_diag_zero_proof {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (hdiag : ∀ i, M i i = 0) : M = 0 := by
  ext i j
  have hsub : (M.submatrix ![i, j] ![i, j]).PosSemidef := hM.submatrix _
  have hdet := hsub.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, hdiag] at hdet
  have hsymm : M j i = M i j := by
    simpa using (hM.1.apply j i).symm
  rw [hsymm] at hdet
  have : M i j * M i j = 0 := by nlinarith
  exact mul_self_eq_zero.mp this

/-- **Negative diagonal gives a certificate.** -/
theorem exists_neg_vector_of_diag_neg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {i : Fin n}
    (h : M i i < 0) : ∃ v : Fin n → ℝ, v ⬝ᵥ (M *ᵥ v) < 0 := by
  refine ⟨fun k => if k = i then 1 else 0, ?_⟩
  have hval : (fun k : Fin n => if k = i then (1 : ℝ) else 0) ⬝ᵥ
      (M *ᵥ (fun k : Fin n => if k = i then (1 : ℝ) else 0)) = M i i := by
    rw [dotProduct]
    simp only [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · intro j _ hji
      simp [hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hval]
  exact h

/-- **Zero diagonal and nonzero: a certificate exists.** -/
theorem exists_neg_vector_of_diag_zero_proof {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) (hdiag : ∀ i, M i i = 0) (hne : M ≠ 0) :
    ∃ v : Fin n → ℝ, v ⬝ᵥ (M *ᵥ v) < 0 := by
  by_contra hcon
  push_neg at hcon
  exact hne (eq_zero_of_posSemidef_diag_zero_proof
    (posSemidef_iff_dotProduct_mulVec.mpr ⟨hM, hcon⟩) hdiag)

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (hdiag : ∀ i, M i i = 0) : M = 0 :=
  ModernConvex.Relaxations.eq_zero_of_posSemidef_diag_zero_proof hM hdiag
