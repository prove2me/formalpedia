-- Prove2me | solution 1 for LinearOptimization.ellipsoidUpdateCenter_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:04.230762+00:00
-- url     : https://prove2.me/submissions/e910965a-dcbe-4a07-af35-40ff69c4062c

import Mathlib
import Definitions.Def_LinearOptimization_EllipsoidMethod

open Matrix
open scoped BigOperators

namespace LinearOptimization

/-- The quadratic form `a ⬝ᵥ (D *ᵥ a)` scales by `c²`. -/
theorem dotProduct_mulVec_smul {n : ℕ} (c : ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) :
    (c • a) ⬝ᵥ (D *ᵥ (c • a)) = c ^ 2 * (a ⬝ᵥ (D *ᵥ a)) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  ring

/-- `vecMulVec` scales quadratically. -/
theorem vecMulVec_smul_smul {m n : ℕ} (c : ℝ) (w : Fin m → ℝ) (v : Fin n → ℝ) :
    Matrix.vecMulVec (c • w) (c • v) = (c ^ 2) • Matrix.vecMulVec w v := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **The normalised direction is scale invariant.** -/
theorem sqrt_inv_smul_mulVec {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) {c : ℝ}
    (hc : 0 < c) :
    (Real.sqrt ((c • a) ⬝ᵥ (D *ᵥ (c • a))))⁻¹ • (D *ᵥ (c • a))
      = (Real.sqrt (a ⬝ᵥ (D *ᵥ a)))⁻¹ • (D *ᵥ a) := by
  rw [dotProduct_mulVec_smul, Matrix.mulVec_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le,
    mul_inv, smul_smul]
  rw [show c⁻¹ * (Real.sqrt (a ⬝ᵥ (D *ᵥ a)))⁻¹ * c
      = (Real.sqrt (a ⬝ᵥ (D *ᵥ a)))⁻¹ by field_simp]

/-- **The centre update is invariant under positive rescaling of the cut.** -/
theorem ellipsoidUpdateCenter_smul_proof {n : ℕ} (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    ellipsoidUpdateCenter z D (c • a) = ellipsoidUpdateCenter z D a := by
  unfold ellipsoidUpdateCenter
  rw [sqrt_inv_smul_mulVec D a hc]

/-- **The matrix update is invariant under positive rescaling of the cut.** -/
theorem ellipsoidUpdateMatrix_smul {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ)
    {c : ℝ} (hc : 0 < c) :
    ellipsoidUpdateMatrix D (c • a) = ellipsoidUpdateMatrix D a := by
  unfold ellipsoidUpdateMatrix
  rw [dotProduct_mulVec_smul, vecMulVec_smul_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    smul_smul]
  rw [show (2 : ℝ) / ((n : ℝ) + 1) * (c ^ 2 * (a ⬝ᵥ (D *ᵥ a)))⁻¹ * c ^ 2
      = 2 / ((n : ℝ) + 1) * (a ⬝ᵥ (D *ᵥ a))⁻¹ by field_simp]
  rw [smul_smul]

end LinearOptimization

open LinearOptimization in
theorem solution {n : ℕ} (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ)
    (a : Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    ellipsoidUpdateCenter z D (c • a) = ellipsoidUpdateCenter z D a :=
  LinearOptimization.ellipsoidUpdateCenter_smul_proof z D a hc

