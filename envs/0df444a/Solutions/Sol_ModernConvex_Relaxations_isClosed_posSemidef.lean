-- Prove2me | solution 1 for ModernConvex.Relaxations.isClosed_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:52:11.72591+00:00
-- url     : https://prove2.me/submissions/33853402-0928-49fb-b248-577c91744a98

import Mathlib

/-!
# The positive semidefinite cone is closed and convex

The primal body of the Max-Cut semidefinite relaxation is `{X : X ⪰ 0, X_ii = 1}`. Two of the
three `IsConvexBody` requirements are about the cone of positive semidefinite matrices:

* **closedness** — this file proves `IsClosed {X | X.PosSemidef}`. The set is the intersection of
  the closed set of symmetric matrices (an equalizer of two continuous maps, `X ↦ X` and
  `X ↦ Xᴴ`) with the sets `{X | 0 ≤ v ⬝ᵥ (X *ᵥ v)}`, one for each `v`, each closed because
  `X ↦ v ⬝ᵥ (X *ᵥ v)` is continuous. Mathlib has no closedness statement for `PosSemidef`;
  the spectral characterisation would need eigenvalue continuity, so the quadratic-form
  characterisation is used instead — it costs nothing because the intersection is allowed to be
  uncountable.
* **convexity** — `PosSemidef` is closed under nonnegative linear combinations, proved directly
  from the quadratic form.

Also recorded: every positive semidefinite matrix with unit diagonal has entries of absolute value
at most one (`|X_ij|² ≤ X_ii X_jj = 1`), which is what makes the body bounded.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- `X ↦ v ⬝ᵥ (X *ᵥ v)` is continuous in `X`. -/
theorem continuous_quadraticForm {n : ℕ} (v : Fin n → ℝ) :
    Continuous fun X : Matrix (Fin n) (Fin n) ℝ => v ⬝ᵥ (X *ᵥ v) := by
  have h : ∀ X : Matrix (Fin n) (Fin n) ℝ, v ⬝ᵥ (X *ᵥ v) = ∑ i, ∑ j, v i * (X i j * v j) := by
    intro X
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  simp only [h]
  fun_prop

/-- **The positive semidefinite cone is closed.** -/
theorem isClosed_posSemidef_proof {n : ℕ} :
    IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} := by
  have hHerm : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.IsHermitian} :=
    isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id
  have hQuad : IsClosed {X : Matrix (Fin n) (Fin n) ℝ |
      ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (X *ᵥ v)} := by
    have hset : {X : Matrix (Fin n) (Fin n) ℝ | ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (X *ᵥ v)}
        = ⋂ v : Fin n → ℝ, {X : Matrix (Fin n) (Fin n) ℝ | 0 ≤ v ⬝ᵥ (X *ᵥ v)} := by
      ext X
      simp
    rw [hset]
    exact isClosed_iInter fun v => isClosed_le continuous_const (continuous_quadraticForm v)
  have hPSD : {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef}
      = {X : Matrix (Fin n) (Fin n) ℝ | X.IsHermitian} ∩
        {X : Matrix (Fin n) (Fin n) ℝ | ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (X *ᵥ v)} := by
    ext X
    exact posSemidef_iff_dotProduct_mulVec
  rw [hPSD]
  exact hHerm.inter hQuad

/-- **The positive semidefinite cone is convex.** -/
theorem posSemidef_add_smul {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a • X + b • Y).PosSemidef := by
  have hX' : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ X := hX.nonneg
  have hY' : (0 : Matrix (Fin n) (Fin n) ℝ) ≤ Y := hY.nonneg
  exact (add_nonneg (smul_nonneg ha hX') (smul_nonneg hb hY')).posSemidef

/-- **Boundedness of the primal body.** A positive semidefinite matrix with unit diagonal has
`|X_ij| ≤ 1`: the `2 × 2` principal submatrix on `{i, j}` is positive semidefinite, so its
determinant `X_ii X_jj − X_ij²` is nonnegative. -/
theorem abs_entry_le_one {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (hdiag : ∀ k, X k k = 1) (i j : Fin n) : |X i j| ≤ 1 := by
  have hsub : (X.submatrix ![i, j] ![i, j]).PosSemidef := hX.submatrix _
  have hdet := hsub.det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hdet
  have hsymm : X j i = X i j := by
    simpa using (hX.1.apply j i).symm
  rw [hsymm, hdiag i, hdiag j] at hdet
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (X i j), hdet]

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} :=
  ModernConvex.Relaxations.isClosed_posSemidef_proof
