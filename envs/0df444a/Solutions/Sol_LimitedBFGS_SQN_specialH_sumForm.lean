-- Prove2me | solution 1 for LimitedBFGS.SQN.specialH_sumForm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T00:36:33.818087+00:00
-- url     : https://prove2.me/submissions/8a222eba-ee32-4bce-bf26-e46e93642a0d

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_specialH

open Matrix
open LimitedBFGS.SQN

namespace LimitedBFGS.SQN

/-- `v ᵀ = 1 - rho * (s * yᵀ)`. -/
private theorem bfgsV_transpose {n : ℕ} (s y : Fin n → ℝ) :
    (bfgsV s y)ᵀ = 1 - bfgsRho s y • vecMulVec s y := by
  simp [bfgsV, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_vecMulVec]

/-- `s yᵀ * H * (y sᵀ) = (yᵀ H y) s sᵀ`. -/
private theorem collapse {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ) :
    vecMulVec s y * H * vecMulVec y s = (y ⬝ᵥ (H *ᵥ y)) • vecMulVec s s := by
  rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  exact congrArg (fun v => v • vecMulVec s s) (Matrix.dotProduct_mulVec y H y).symm

/-- `(I - rho s yᵀ) * H * (I - rho y sᵀ)` equals
`H - rho (s yᵀ H + H y sᵀ) + (rho² yᵀHy) s sᵀ`. -/
private theorem expand_prod {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s y : Fin n → ℝ)
    (ρ : ℝ) (hρ : ρ = bfgsRho s y) :
    (1 - ρ • vecMulVec s y) * H * (1 - ρ • vecMulVec y s)
      = H - ρ • (vecMulVec s y * H + H * vecMulVec y s)
        + (ρ ^ 2 * (y ⬝ᵥ (H *ᵥ y))) • vecMulVec s s := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (vecMulVec s y) H (vecMulVec y s), collapse, smul_smul]
  ext i j
  simp only [vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.sub_apply, Matrix.add_apply]
  ring

/-- The product form and the sum form of the BFGS update coincide:
`v ᵀ H v + rho s sᵀ = H + U(s, y, H)`. -/
private theorem bfgsStep_eq_add_bfgsU {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (s y : Fin n → ℝ) : bfgsStep H s y = H + bfgsU H s y := by
  rw [bfgsStep, bfgsU, bfgsV_transpose, bfgsV]
  rw [expand_prod H s y (bfgsRho s y) rfl]
  unfold bfgsRho
  ext i j
  simp only [vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.sub_apply]
  ring

/-- Folding `f` over `l.map g` equals folding `fun a x => f a (g x)` over `l`. -/
private theorem foldl_map_eq {α β γ : Type*} (l : List α) (f : β → γ → β)
    (g : α → γ) (b : β) :
    (l.map g).foldl f b = l.foldl (fun acc x => f acc (g x)) b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [ih]

/-- Folds with pointwise-equal steps agree. -/
private theorem foldl_congr {α β : Type*} (l : List α) (f g : β → α → β)
    (b : β) (hf : ∀ acc x, f acc x = g acc x) : l.foldl f b = l.foldl g b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
      simp only [List.foldl_cons, hf]
      rw [ih]

end LimitedBFGS.SQN

theorem solution {n : ℕ} (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef)
    (m : ℕ) (hm : 1 ≤ m) (s y : ℕ → Fin n → ℝ) (hys : ∀ i, 0 < y i ⬝ᵥ s i)
    (k : ℕ) (hk : m ≤ k) :
    specialH H₀ m s y (k + 1) =
      (List.range' (k + 1 - m) m).foldl (fun H j => H + bfgsU H (s j) (y j)) H₀ := by
  have hmin : min (k + 1) m = m := by omega
  set σ := k + 1 - m with hσ
  simp only [specialH, specialHList, hmin]
  have hl : (List.map (fun i => (s (σ + i), y (σ + i))) (List.range m)).foldl
        (fun H p => bfgsStep H p.1 p.2) H₀
      = (List.range m).foldl (fun H i => bfgsStep H (s (σ + i)) (y (σ + i))) H₀ :=
    foldl_map_eq _ _ _ H₀
  have hr : (List.range' σ m).foldl (fun H j => H + bfgsU H (s j) (y j)) H₀
      = (List.range m).foldl (fun H i => H + bfgsU H (s (σ + i)) (y (σ + i))) H₀ := by
    rw [List.range'_eq_map_range]
    exact foldl_map_eq _ _ _ H₀
  have hpt : ∀ (H : Matrix (Fin n) (Fin n) ℝ) (i : ℕ),
      bfgsStep H (s (σ + i)) (y (σ + i)) = H + bfgsU H (s (σ + i)) (y (σ + i)) :=
    fun H i => bfgsStep_eq_add_bfgsU H (s (σ + i)) (y (σ + i))
  rw [hl, hr]
  exact foldl_congr _ _ _ H₀ hpt
