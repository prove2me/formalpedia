-- Prove2me | solution 1 for MosonyiPetz.schwarz_inequality
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-15T18:18:10.059648+00:00
-- url     : https://prove2.me/submissions/584c5dea-f6c2-45da-9ea0-fe808c8143a5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

open Matrix
open scoped Matrix ComplexOrder MatrixOrder
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)

namespace SchwarzAux

/-- A Hermitian matrix is a difference of two positive semidefinite matrices. -/
theorem exists_posSemidef_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) :
    ∃ P N : Matrix ι ι ℂ, P.PosSemidef ∧ N.PosSemidef ∧ A = P - N := by
  refine ⟨cfc (fun x : ℝ => max x 0) A, cfc (fun x : ℝ => max (-x) 0) A,
    Matrix.LE.le.posSemidef (cfc_nonneg fun x _ => le_max_right _ _),
    Matrix.LE.le.posSemidef (cfc_nonneg fun x _ => le_max_right _ _), ?_⟩
  rw [← cfc_sub _ _ A (Matrix.finite_real_spectrum.continuousOn _)
    (Matrix.finite_real_spectrum.continuousOn _),
    cfc_congr (f := fun x : ℝ => max x 0 - max (-x) 0) (g := fun x : ℝ => x) fun x _ => by
      show max x 0 - max (-x) 0 = x
      rcases le_total 0 x with hx | hx
      · rw [max_eq_left hx, max_eq_right (by linarith), sub_zero]
      · rw [max_eq_right hx, max_eq_left (by linarith), zero_sub, neg_neg]]
  exact (cfc_id' ℝ A hA).symm

/-- A positive map is `*`-preserving. -/
theorem conjTranspose_map_of_posSemidef {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ}
    (hΦ : ∀ M : Matrix ι ι ℂ, M.PosSemidef → (Φ M).PosSemidef) (X : Matrix ι ι ℂ) :
    Φ Xᴴ = (Φ X)ᴴ := by
  have hherm : ∀ A : Matrix ι ι ℂ, A.IsHermitian → (Φ A).IsHermitian := by
    intro A hA
    obtain ⟨P, N, hP, hN, rfl⟩ := exists_posSemidef_sub hA
    rw [map_sub]
    exact (hΦ P hP).isHermitian.sub (hΦ N hN).isHermitian
  obtain ⟨A, B, hA, hB, hX, hXh⟩ : ∃ A B : Matrix ι ι ℂ, A.IsHermitian ∧ B.IsHermitian ∧
      (2 : ℂ) • X = A - Complex.I • B ∧ (2 : ℂ) • Xᴴ = A + Complex.I • B := by
    refine ⟨X + Xᴴ, Complex.I • (X - Xᴴ), ?_, ?_, ?_, ?_⟩
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
        add_comm]
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_I,
        neg_smul, ← smul_neg, neg_sub]
    · rw [smul_smul, Complex.I_mul_I]
      module
    · rw [smul_smul, Complex.I_mul_I]
      module
  have hstar2 : star (2 : ℂ) = 2 := by norm_num
  have e1 : (2 : ℂ) • Φ Xᴴ = Φ A + Complex.I • Φ B := by
    rw [← LinearMap.map_smul, hXh, map_add, LinearMap.map_smul]
  have e2 : (2 : ℂ) • (Φ X)ᴴ = ((2 : ℂ) • Φ X)ᴴ := by
    rw [Matrix.conjTranspose_smul, hstar2]
  have e3 : (2 : ℂ) • Φ X = Φ A - Complex.I • Φ B := by
    rw [← LinearMap.map_smul, hX, map_sub, LinearMap.map_smul]
  have key : (2 : ℂ) • Φ Xᴴ = (2 : ℂ) • (Φ X)ᴴ := by
    rw [e1, e2, e3, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def,
      Complex.conj_I, hherm A hA, hherm B hB, neg_smul, sub_neg_eq_add]
  exact smul_right_injective _ two_ne_zero key

/-- The `(e, e')` block of a matrix on a product index. -/
def blockOf {ι ιE : Type*} (M : Matrix (ιE × ι) (ιE × ι) ℂ) (e e' : ιE) : Matrix ι ι ℂ :=
  Matrix.of fun i i' => M (e, i) (e', i')

/-- A family of blocks assembled into a matrix whose row index is a product. -/
def ofBlockCol {ι ι' ιE : Type*} (C : ιE → Matrix ι ι' ℂ) : Matrix (ιE × ι) ι' ℂ :=
  Matrix.of fun p j => C p.1 p.2 j

theorem blockOf_ofBlockCol_mul_conjTranspose {ι ι' ιE : Type*} [Fintype ι']
    (N : ιE → Matrix ι ι' ℂ) (a b : ιE) :
    blockOf (ofBlockCol N * (ofBlockCol N)ᴴ) a b = N a * (N b)ᴴ := by
  ext i j
  simp [blockOf, ofBlockCol, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem conjTranspose_ofBlockCol_mul_mul {ι ι' ιE : Type*} [Fintype ι] [Fintype ιE]
    (K : Matrix (ιE × ι) (ιE × ι) ℂ) (C D : ιE → Matrix ι ι' ℂ) :
    (ofBlockCol C)ᴴ * K * ofBlockCol D
      = ∑ a : ιE, ∑ b : ιE, (C a)ᴴ * blockOf K a b * D b := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.conjTranspose_apply, blockOf, ofBlockCol,
    Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_mul]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

theorem blockOf_idTensorSuperop {ι κ ιE : Type*} (Φ : Matrix ι ι ℂ → Matrix κ κ ℂ)
    (M : Matrix (ιE × ι) (ιE × ι) ℂ) (e e' : ιE) :
    blockOf (QAlgorithms.idTensorSuperop (R := ιE) Φ M) e e' = Φ (blockOf M e e') := rfl

end SchwarzAux

open SchwarzAux in
theorem solution {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (τ : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (hτ : IsTwoPositive τ) (h1 : τ 1 = 1)
    (A : Matrix H H ℂ) :
    (τ (Aᴴ * A) - (τ A)ᴴ * τ A).PosSemidef := by
  have hpos : ∀ X : Matrix H H ℂ, X.PosSemidef → (τ X).PosSemidef := fun X hX =>
    (hτ _ (hX.submatrix (Prod.snd : Fin 2 × H → H))).submatrix fun i : K => ((0 : Fin 2), i)
  have hstar := conjTranspose_map_of_posSemidef hpos
  have hK := hτ _ (Matrix.posSemidef_self_mul_conjTranspose
    (ofBlockCol (fun a : Fin 2 => if a = 0 then Aᴴ else (1 : Matrix H H ℂ))))
  have hcong := hK.conjTranspose_mul_mul_same
    (ofBlockCol (fun a : Fin 2 => if a = 0 then (1 : Matrix K K ℂ) else -(τ A)))
  rw [conjTranspose_ofBlockCol_mul_mul] at hcong
  simp only [Fin.sum_univ_two, blockOf_idTensorSuperop,
    blockOf_ofBlockCol_mul_conjTranspose] at hcong
  norm_num [h1, Matrix.conjTranspose_conjTranspose] at hcong
  rw [hstar A, ← sub_eq_add_neg] at hcong
  exact hcong
