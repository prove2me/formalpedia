-- Prove2me | solution 1 for LesHouchesWidth.gaussian_linear_image
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T22:22:54.900973+00:00
-- url     : https://prove2.me/submissions/2763c3fa-635a-4d36-99f6-36a307bef2be

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP
import Definitions.Def_LesHouchesWidth_FiniteWidth

open MeasureTheory ProbabilityTheory Matrix

set_option autoImplicit false

theorem solution {k d : ℕ} (μ : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (A : Matrix (Fin k) (Fin d) ℝ) :
    (multivariateGaussian μ S).map (Matrix.toEuclideanLin A) =
      multivariateGaussian (Matrix.toEuclideanLin A μ) (A * S * A.transpose) := by
  let L := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hcov : (A * S * A.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.mul_mul_conjTranspose_same A
  change (multivariateGaussian μ S).map L = multivariateGaussian (L μ) _
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian,
      integral_id_multivariateGaussian]
    exact IsGaussian.integrable_id
  · ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hS, covarianceBilin_multivariateGaussian hcov]
    have hadj : L.adjoint = (Matrix.toEuclideanLin A.transpose).toContinuousLinearMap := by
      simp only [L, ← LinearMap.adjoint_toContinuousLinearMap,
        ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [hadj]
    change (A.transpose *ᵥ x) ⬝ᵥ S *ᵥ (A.transpose *ᵥ y) =
      x ⬝ᵥ (A * S * A.transpose) *ᵥ y
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
