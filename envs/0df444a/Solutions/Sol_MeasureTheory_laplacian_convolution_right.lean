-- Prove2me | solution 1 for MeasureTheory.laplacian_convolution_right
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T22:38:44.817005+00:00
-- url     : https://prove2.me/submissions/d2ed87a4-a3e6-422c-86c9-9278ab176f36

import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff
open Laplacian

theorem solution (n : ℕ) (K f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : LocallyIntegrable K volume) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    Δ (K ⋆[lsmul ℝ ℝ] f) = K ⋆[lsmul ℝ ℝ] (Δ f) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := lsmul ℝ ℝ
  have hd (g : E → ℝ) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
      (x v : E) :
      fderiv ℝ (K ⋆[L] g) x v = (K ⋆[L] (fun y => fderiv ℝ g y v)) x := by
    rw [(hgc.hasFDerivAt_convolution_right L hK hg x).fderiv]
    exact convolution_precompR_apply L hK (hgc.fderiv ℝ)
      (hg.continuous_fderiv one_ne_zero) x v
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hsecond (x v : E) :
      iteratedFDeriv ℝ 2 (K ⋆[L] f) x ![v,v] =
        (K ⋆[L] (fun y => iteratedFDeriv ℝ 2 f y ![v,v])) x := by
    have heq : (fun y => fderiv ℝ (K ⋆[L] f) y v) =
        K ⋆[L] (fun y => fderiv ℝ f y v) := funext fun y => hd f (hf.of_le (by norm_num)) hfc y v
    have hc : HasCompactSupport (fun y => fderiv ℝ f y v) :=
      (hfc.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℝ => A v) (by simp)
    have hdiff : Differentiable ℝ (fderiv ℝ (K ⋆[L] f)) :=
      ((hfc.contDiff_convolution_right L hK hf).fderiv_right (by norm_num) :
        ContDiff ℝ 1 (fderiv ℝ (K ⋆[L] f))).differentiable one_ne_zero
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have happ (g : E → ℝ) (hg : Differentiable ℝ (fderiv ℝ g)) (y : E) :
        fderiv ℝ (fun z => fderiv ℝ g z v) y v = fderiv ℝ (fderiv ℝ g) y v v := by
      simp [fderiv_clm_apply (hg y) (differentiableAt_const v)]
    rw [← happ _ hdiff, heq, hd _ (hdf.clm_apply contDiff_const) hc]
    congr 1
    funext y
    exact happ f (hdf.differentiable one_ne_zero) y
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  dsimp only [L] at hsecond
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  ext x
  simp only [hsecond, convolution_def]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
  simp only [lsmul_apply, smul_eq_mul]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => (Finset.mul_sum ..).symm
  · intro i hi
    exact ((hfc.iteratedFDeriv (𝕜 := ℝ) 2).comp_left
      (g := fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ => A ![b i,b i])
      (by simp)).convolutionExists_right L hK (hf.continuous_iteratedFDeriv'.eval continuous_const) x
