-- Prove2me | solution 1 for IAFTRL.lemma_C_4
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-14T14:51:38.544763+00:00
-- url     : https://prove2.me/submissions/67e22b9f-92f3-456d-8ecc-1701e84430dc

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

open Matrix Finset Polynomial
set_option maxHeartbeats 1000000

namespace C4Proof

/-- The top coefficient in the principal-minor expansion. -/
private lemma top_coeff {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ) :
    (det (1 + (X : ℝ[X]) • M.map C)).coeff r = M.det := by
  rw [coeff_det_one_add_X_smul_eq_sum_minors]
  have hc : r = (univ : Finset (Fin r)).card := by simp
  have hp : (univ : Finset (Fin r)).powersetCard r = {univ} := by
    conv_lhs => arg 1; rw [hc]
    exact powersetCard_self _
  rw [hp, sum_singleton]
  let e : (univ : Finset (Fin r)) ≃ Fin r :=
    ⟨Subtype.val, fun i => ⟨i, mem_univ i⟩, fun _ => rfl, fun _ => rfl⟩
  exact det_submatrix_equiv_self e M

/-- Rectangular Cauchy–Binet, obtained by comparing coefficients in
`det (1 + tAB) = det (1 + tBA)`. Subsets use the target's increasing row order. -/
private lemma cauchy_binet {m r : ℕ}
    (A : Matrix (Fin r) (Fin m) ℝ) (B : Matrix (Fin m) (Fin r) ℝ) :
    (A * B).det = ∑ I : {I : Finset (Fin m) // I.card = r},
      (A.submatrix id (I.1.orderEmbOfFin I.2)).det *
      (B.submatrix (I.1.orderEmbOfFin I.2) id).det := by
  classical
  have h := det_one_add_mul_comm ((X : ℝ[X]) • A.map C) (B.map C)
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul] at h
  have hh := congrArg (fun p : ℝ[X] => p.coeff r) h
  rw [top_coeff, coeff_det_one_add_X_smul_eq_sum_minors] at hh
  rw [hh]
  rw [Finset.sum_subtype (p := fun I : Finset (Fin m) => I.card = r)
    _ (by simp [mem_powersetCard])]
  apply sum_congr rfl
  intro I _
  let e := (I.1.orderIsoOfFin I.2).toEquiv
  rw [← det_submatrix_equiv_self e]
  have hsub : ((B * A).submatrix Subtype.val Subtype.val).submatrix e e =
      B.submatrix (I.1.orderEmbOfFin I.2) id *
      A.submatrix id (I.1.orderEmbOfFin I.2) := by
    ext i j
    rfl
  rw [hsub, det_mul, mul_comm]

end C4Proof

/-- Weighted least squares is a convex combination of nonsingular interpolants. -/
theorem solution {m r : ℕ} (x : Fin m → Fin r → ℝ) (z w : Fin m → ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hV : (∑ a, w a • vecMulVec (x a) (x a)).PosDef) :
    let V : Matrix (Fin r) (Fin r) ℝ := ∑ a, w a • vecMulVec (x a) (x a)
    let B : {I : Finset (Fin m) // I.card = r} → Matrix (Fin r) (Fin r) ℝ :=
      fun I => Matrix.of fun i k => x (I.1.orderEmbOfFin I.2 i) k
    let vI : {I : Finset (Fin m) // I.card = r} → Fin r → ℝ :=
      fun I => (B I)⁻¹ *ᵥ fun i => z (I.1.orderEmbOfFin I.2 i)
    let ωI : {I : Finset (Fin m) // I.card = r} → ℝ :=
      fun I => (B I).det ^ 2 * (∏ a ∈ I.1, w a) / V.det
    V⁻¹ *ᵥ (∑ a, (w a * z a) • x a) =
        ∑ I ∈ Finset.univ.filter (fun I => (B I).det ≠ 0), ωI I • vI I ∧
      (∀ I, 0 ≤ ωI I) ∧
      ∑ I ∈ Finset.univ.filter (fun I => (B I).det ≠ 0), ωI I = 1 := by
  classical
  dsimp only
  let V : Matrix (Fin r) (Fin r) ℝ := ∑ a, w a • vecMulVec (x a) (x a)
  let B (I : {I : Finset (Fin m) // I.card = r}) : Matrix (Fin r) (Fin r) ℝ :=
    Matrix.of fun i k => x (I.1.orderEmbOfFin I.2 i) k
  let W (I : {I : Finset (Fin m) // I.card = r}) := ∏ a ∈ I.1, w a
  let A : Matrix (Fin r) (Fin m) ℝ := Matrix.of fun k a => w a * x a k
  let Xmat : Matrix (Fin m) (Fin r) ℝ := x
  let b : Fin r → ℝ := ∑ a, (w a * z a) • x a
  let S := Finset.univ.filter (fun I : {I : Finset (Fin m) // I.card = r} =>
    (B I).det ≠ 0)
  have hpos : 0 < V.det := hV.det_pos
  have hne : V.det ≠ 0 := ne_of_gt hpos
  have hAX : A * Xmat = V := by
    ext i j
    change (∑ a, w a * x a i * x a j) =
      (∑ a, w a • vecMulVec (x a) (x a)) i j
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
    apply sum_congr rfl
    intro a _
    ring
  have hAz : A *ᵥ z = b := by
    ext i
    simp only [A, b, mulVec, dotProduct, of_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    apply sum_congr rfl
    intro a _
    ring
  have hAdet (I : {I : Finset (Fin m) // I.card = r}) :
      (A.submatrix id (I.1.orderEmbOfFin I.2)).det = W I * (B I).det := by
    have hp : (∏ i, w (I.1.orderEmbOfFin I.2 i)) = W I := by
      calc
        _ = ∏ a : I.1, w a :=
          (I.1.orderIsoOfFin I.2).toEquiv.prod_comp (fun a : I.1 => w a)
        _ = W I := Finset.prod_coe_sort _ _
    change (Matrix.of fun i j => w (I.1.orderEmbOfFin I.2 j) *
      (B I)ᵀ i j).det = _
    rw [det_mul_row, det_transpose, hp]
  have hdet : V.det = ∑ I, (B I).det ^ 2 * W I := by
    rw [← hAX, C4Proof.cauchy_binet]
    apply sum_congr rfl
    intro I _
    rw [hAdet]
    change W I * (B I).det * (B I).det = _
    ring
  have hdetS : V.det = ∑ I ∈ S, (B I).det ^ 2 * W I := by
    rw [hdet]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro I _ hi
    have hz : (B I).det = 0 := by simpa [S] using hi
    simp [hz]
  have hweights : ∀ I, 0 ≤ (B I).det ^ 2 * W I / V.det := by
    intro I
    exact div_nonneg (mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun a _ => hw a))
      hpos.le
  have hsum : ∑ I ∈ S, (B I).det ^ 2 * W I / V.det = 1 := by
    rw [← sum_div, ← hdetS, div_self hne]
  refine ⟨?_, hweights, hsum⟩
  -- Apply Cramer's rule coordinatewise, dropping singular minors before cancellation.
  change V⁻¹ *ᵥ b = ∑ I ∈ S,
    ((B I).det ^ 2 * W I / V.det) •
      ((B I)⁻¹ *ᵥ fun i => z (I.1.orderEmbOfFin I.2 i))
  ext k
  have hcramer (M : Matrix (Fin r) (Fin r) ℝ) (y : Fin r → ℝ)
      (hm : M.det ≠ 0) :
      M.det * (M⁻¹ *ᵥ y) k = (M.updateCol k y).det := by
    simpa only [smul_mulVec, Pi.smul_apply, smul_eq_mul, cramer_apply] using
      congrFun (det_smul_inv_mulVec_eq_cramer M y (isUnit_iff_ne_zero.mpr hm)) k
  have hnum : (V.updateCol k b).det = ∑ I,
      W I * (B I).det *
        ((B I).updateCol k (fun i => z (I.1.orderEmbOfFin I.2 i))).det := by
    rw [← hAX, ← hAz, ← mul_updateCol, C4Proof.cauchy_binet]
    apply sum_congr rfl
    intro I _
    rw [hAdet]
    congr 2
  have hnumS : (V.updateCol k b).det = ∑ I ∈ S,
      W I * (B I).det *
        ((B I).updateCol k (fun i => z (I.1.orderEmbOfFin I.2 i))).det := by
    rw [hnum]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro I _ hi
    have hz : (B I).det = 0 := by simpa [S] using hi
    simp [hz]
  apply (mul_left_cancel₀ hne)
  rw [hcramer V b hne, hnumS]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro I hi
  have hi' : (B I).det ≠ 0 := (mem_filter.mp hi).2
  rw [← hcramer (B I) _ hi']
  field_simp
