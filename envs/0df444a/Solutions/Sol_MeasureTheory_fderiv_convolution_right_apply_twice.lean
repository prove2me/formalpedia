-- Prove2me | solution 1 for MeasureTheory.fderiv_convolution_right_apply_twice
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:11:45.739436+00:00
-- url     : https://prove2.me/submissions/e0c6d405-975a-4313-8043-b007fa374b81

import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory ContinuousLinearMap
open scoped Convolution ContDiff

theorem solution (n : ℕ) (K f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : LocallyIntegrable K volume) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (x v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => fderiv ℝ (K ⋆[lsmul ℝ ℝ] f) z w) x v =
      (K ⋆[lsmul ℝ ℝ] (fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v)) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := lsmul ℝ ℝ
  have hd (g : E → ℝ) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
      (y a : E) :
      fderiv ℝ (K ⋆[L] g) y a = (K ⋆[L] (fun z => fderiv ℝ g z a)) y := by
    rw [(hgc.hasFDerivAt_convolution_right L hK hg y).fderiv]
    exact convolution_precompR_apply L hK (hgc.fderiv ℝ)
      (hg.continuous_fderiv one_ne_zero) y a
  have heq : (fun z => fderiv ℝ (K ⋆[L] f) z w) =
      K ⋆[L] (fun z => fderiv ℝ f z w) :=
    funext fun z => hd f (hf.of_le (by norm_num)) hfc z w
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hc : HasCompactSupport (fun z => fderiv ℝ f z w) :=
    (hfc.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℝ => A w) (by simp)
  change fderiv ℝ (fun z => fderiv ℝ (K ⋆[L] f) z w) x v = _
  rw [heq, hd _ (hdf.clm_apply contDiff_const) hc]
