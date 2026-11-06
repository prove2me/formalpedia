-- Prove2me | solution 1 for ModernConvex.Relaxations.matOfUpper_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:01:10.012999+00:00
-- url     : https://prove2.me/submissions/da6e3be7-f1e5-428d-9e6a-997c2323ea1b

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_Upper

/-!
# Free coordinates for the Max-Cut SDP body: the strict upper triangle

The primal body `{X : X ⪰ 0, X_ii = 1}` lies in the affine subspace of matrices with unit
diagonal, so it has empty interior in the space of all matrices and cannot be a convex body in
the sense required by the ellipsoid method. The fix is to eliminate the diagonal constraints: a
symmetric matrix with unit diagonal is determined by its strict upper triangle, through the affine
map `matOfUpper`. In these coordinates the body `{z | matOfUpper z ⪰ 0}` is full dimensional: the
quadratic form is `Σ v_i² + Σ_{i≠j} z_ij v_i v_j`, so `|z| ≤ B` with `B n ≤ 1` already forces
positive semidefiniteness. This file proves that interior statement.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- Off-diagonal entries of `matOfUpper z` are upper-triangular coordinates. -/
theorem abs_upperOff_le {n : ℕ} {z : UpIdx n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ p, |z p| ≤ B) (i j : Fin n) : |upperOff z i j| ≤ B := by
  by_cases h : i = j
  · subst h
    rw [upperOff_diag, abs_zero]
    exact hB
  · simp only [upperOff, Matrix.of_apply, if_neg h]
    by_cases hij : i < j
    · rw [matOfUpper, Matrix.of_apply, dif_pos hij]
      exact hz _
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm h)
      rw [matOfUpper, Matrix.of_apply, dif_neg hij, dif_pos hji]
      exact hz _

/-- The quadratic form of the off-diagonal part is bounded by `B (Σ |v_i|)²`. -/
theorem abs_quadform_upperOff_le {n : ℕ} {z : UpIdx n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ p, |z p| ≤ B) (v : Fin n → ℝ) :
    |v ⬝ᵥ (upperOff z *ᵥ v)| ≤ B * (∑ i, |v i|) ^ 2 := by
  have hterm : ∀ i j : Fin n, |v i * (upperOff z i j * v j)| ≤ B * (|v i| * |v j|) := by
    intro i j
    have h1 : |v i * (upperOff z i j * v j)| = |v i| * |upperOff z i j| * |v j| := by
      rw [abs_mul, abs_mul, mul_assoc]
    have h2 : |upperOff z i j| ≤ B := abs_upperOff_le hB hz i j
    have hvi : (0:ℝ) ≤ |v i| := abs_nonneg _
    have hvj : (0:ℝ) ≤ |v j| := abs_nonneg _
    rw [h1]
    have hstep : |v i| * |upperOff z i j| * |v j| ≤ |v i| * B * |v j| := by
      refine mul_le_mul_of_nonneg_right ?_ hvj
      exact mul_le_mul_of_nonneg_left h2 hvi
    calc |v i| * |upperOff z i j| * |v j|
        ≤ |v i| * B * |v j| := hstep
      _ = B * (|v i| * |v j|) := by ring
  have hsplit : v ⬝ᵥ (upperOff z *ᵥ v) = ∑ i, ∑ j, v i * (upperOff z i j * v j) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  rw [hsplit]
  calc |∑ i, ∑ j, v i * (upperOff z i j * v j)|
      ≤ ∑ i, |∑ j, v i * (upperOff z i j * v j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |v i * (upperOff z i j * v j)| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, B * (|v i| * |v j|) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = B * (∑ i, |v i|) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]

/-- **Small upper-triangular data gives a positive semidefinite matrix.** If `|z p| ≤ B` for every
`p` and `B * n ≤ 1`, then `matOfUpper z ⪰ 0`. -/
theorem matOfUpper_posSemidef_proof {n : ℕ} {z : UpIdx n → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hz : ∀ p, |z p| ≤ B) (hBn : B * n ≤ 1) :
    (matOfUpper z).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨matOfUpper_isHermitian z, fun v => ?_⟩
  have hsplit : v ⬝ᵥ (matOfUpper z *ᵥ v)
      = (∑ i, (v i) ^ 2) + v ⬝ᵥ (upperOff z *ᵥ v) := by
    rw [matOfUpper_eq_one_add, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound := abs_quadform_upperOff_le hB hz v
  have hlow : -(B * (∑ i, |v i|) ^ 2) ≤ v ⬝ᵥ (upperOff z *ᵥ v) := by
    have := neg_abs_le (v ⬝ᵥ (upperOff z *ᵥ v))
    linarith
  have hcs : (∑ i, |v i|) ^ 2 ≤ (n : ℝ) * ∑ i, (v i) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => |v i|)
    simpa [Finset.card_univ, sq_abs] using h
  have hnn : (0:ℝ) ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hBcs : B * (∑ i, |v i|) ^ 2 ≤ B * ((n : ℝ) * ∑ i, (v i) ^ 2) :=
    mul_le_mul_of_nonneg_left hcs hB
  have hnn' : (0:ℝ) ≤ (1 - B * n) * ∑ i, (v i) ^ 2 := by nlinarith
  rw [star_trivial, hsplit]
  linarith

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {z : UpIdx n → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hz : ∀ p, |z p| ≤ B) (hBn : B * n ≤ 1) :
    (matOfUpper z).PosSemidef :=
  ModernConvex.Relaxations.matOfUpper_posSemidef_proof hB hz hBn
