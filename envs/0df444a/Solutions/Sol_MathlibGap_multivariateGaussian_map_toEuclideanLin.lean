-- Prove2me | solution 1 for MathlibGap.multivariateGaussian_map_toEuclideanLin
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T22:13:05.880164+00:00
-- url     : https://prove2.me/submissions/ca9b257e-609f-4251-93dc-fc15670a5546

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped Matrix

theorem solution {m n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) (A : Matrix (Fin m) (Fin n) ℝ) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S).map
        (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) =
      multivariateGaussian 0 (A * S * Aᵀ) := by
  have hS' : (A * S * Aᵀ).PosSemidef := by
    simpa using hS.mul_mul_conjTranspose_same A
  apply IsGaussian.ext
  · simp only [id]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · have hadj : ∀ w : EuclideanSpace ℝ (Fin m),
        ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)).adjoint w).ofLp =
          Aᵀ *ᵥ w.ofLp := by
      intro w
      have h1 := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
      have h2 := congrArg (fun f => (f w).ofLp) h1
      simp only [Matrix.ofLp_toEuclideanLin_apply] at h2
      rw [← ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_toLinearMap]
      simpa using h2.symm
    ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hS', hadj, hadj]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u.ofLp A,
      Matrix.mulVec_transpose]
