-- Prove2me | solution 1 for HighDimProb.RandomProcesses.centered_gaussian_eq_map_pi
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T08:50:18.987196+00:00
-- url     : https://prove2.me/submissions/39e0260f-43e4-4bf9-a87d-c3e68903d2c2

import Mathlib

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace SlepianProof

lemma gaussian_eq_multivariate_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ] :
    μ = multivariateGaussian (∫ x, x ∂μ)
      (LinearMap.toMatrix₂ (EuclideanSpace.basisFun ι ℝ).toBasis
        (EuclideanSpace.basisFun ι ℝ).toBasis (covarianceBilin μ).toBilinForm) := by
  let b := (EuclideanSpace.basisFun ι ℝ).toBasis
  let S := LinearMap.toMatrix₂ b b (covarianceBilin μ).toBilinForm
  have hS : S.PosSemidef :=
    (LinearMap.isPosSemidef_iff_posSemidef_toMatrix b).mp
      (LinearMap.BilinForm.isPosSemidef_iff.mp (isPosSemidef_covarianceBilin (μ := μ)))
  have hr (z : EuclideanSpace ℝ ι) : (⇑(b.repr z) : ι → ℝ) = z.ofLp := by
    funext i
    simp [b, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  apply IsGaussian.ext
  · simp
  · ext x y
    rw [covarianceBilin_multivariateGaussian hS]
    have h := apply_eq_dotProduct_toMatrix₂_mulVec b b
      (covarianceBilin μ).toBilinForm x y
    simpa [S, hr, Function.comp_def] using h

lemma centered_gaussian_eq_map_pi_euclidean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ]
    (hmean : (∫ x, x ∂μ) = 0) :
    ∃ L : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι,
      μ = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map L := by
  let S := LinearMap.toMatrix₂ (EuclideanSpace.basisFun ι ℝ).toBasis
    (EuclideanSpace.basisFun ι ℝ).toBasis (covarianceBilin μ).toBilinForm
  let A := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let e := (EuclideanSpace.equiv ι ℝ).symm
  refine ⟨A.comp e.toContinuousLinearMap, ?_⟩
  rw [gaussian_eq_multivariate_covariance μ, hmean]
  change (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => 0 + A x) = _
  simp only [zero_add]
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma centered_gaussian_eq_map_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ]
    (hmean : (∫ x, x ∂μ) = 0) :
    ∃ L : (ι → ℝ) →L[ℝ] (ι → ℝ),
      μ = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map L := by
  let e := EuclideanSpace.equiv ι ℝ
  let ν := μ.map e.symm
  have hm : (∫ x, x ∂ν) = 0 := by
    change (∫ x, x ∂μ.map e.symm) = 0
    rw [ContinuousLinearEquiv.integral_id_map, hmean, map_zero]
  obtain ⟨A, hA⟩ := centered_gaussian_eq_map_pi_euclidean ν hm
  refine ⟨e.toContinuousLinearMap.comp A, ?_⟩
  have he : ν.map e = μ := by
    change (μ.map e.symm).map e = μ
    rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    have hc : (⇑e ∘ ⇑e.symm) = id := by
      funext x
      exact e.apply_symm_apply x
    rw [hc, Measure.map_id]
  rw [← he, hA, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end SlepianProof

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ]
    (hmean : (∫ x, x ∂μ) = 0) :
    ∃ L : (ι → ℝ) →L[ℝ] (ι → ℝ),
      μ = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map L := by
  exact SlepianProof.centered_gaussian_eq_map_pi μ hmean
