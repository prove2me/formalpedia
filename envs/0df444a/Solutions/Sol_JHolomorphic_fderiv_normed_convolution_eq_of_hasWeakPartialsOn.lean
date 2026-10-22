-- Prove2me | solution 1 for JHolomorphic.fderiv_normed_convolution_eq_of_hasWeakPartialsOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T17:31:16.415992+00:00
-- url     : https://prove2.me/submissions/a8c9f229-cfbb-4d50-9979-b9e5a2b3b879

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension



namespace JHolomorphic

open MeasureTheory Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution

/-- If `uₛ`, `uₜ` are weak partial derivatives on all of `ℂ` of a locally integrable
`u : ℂ → E`, then the partial derivatives of the mollification `ρ ⋆ u` are the
mollifications `ρ ⋆ uₛ` and `ρ ⋆ uₜ`. -/
theorem fderiv_normed_convolution_eq_of_hasWeakPartialsOn_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (ρ : ContDiffBump (0 : ℂ)) {u us ut : ℂ → E}
    (h : HasWeakPartialsOn Set.univ u us ut) (hu : LocallyIntegrable u volume) (z : ℂ) :
    fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u) z 1 =
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] us) z ∧
      fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u) z Complex.I =
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] ut) z := by
  have hwc : HasCompactSupport (ρ.normed volume) := ρ.hasCompactSupport_normed
  have hwd : ContDiff ℝ ∞ (ρ.normed volume) := ρ.contDiff_normed
  have hw1 : ContDiff ℝ 1 (ρ.normed volume) := ρ.contDiff_normed
  have hcd : Continuous (fderiv ℝ (ρ.normed volume)) := hw1.continuous_fderiv one_ne_zero
  have hF : HasFDerivAt (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u)
      ((fderiv ℝ (ρ.normed volume) ⋆[(lsmul ℝ ℝ).precompL ℂ, volume] u) z) z :=
    hwc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hw1 hu z
  -- derivative of the mollification as a convolution
  have hderiv : ∀ v : ℂ, fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u) z v =
      ∫ y, fderiv ℝ (ρ.normed volume) (z - y) v • u y := by
    intro v
    rw [hF.fderiv]
    have hce : ConvolutionExistsAt (fderiv ℝ (ρ.normed volume)) u z
        ((lsmul ℝ ℝ).precompL ℂ) volume :=
      HasCompactSupport.convolutionExists_left (𝕜 := ℝ) (G := ℂ) (μ := volume)
        (E := ℂ →L[ℝ] ℝ) (E' := E) (F := ℂ →L[ℝ] E) ((lsmul ℝ ℝ).precompL ℂ)
        (hwc.fderiv (𝕜 := ℝ)) hcd hu z
    have hint : Integrable (fun t => (lsmul ℝ ℝ).precompL ℂ (fderiv ℝ (ρ.normed volume) t)
        (u (z - t))) volume := hce
    rw [convolution_def, ContinuousLinearMap.integral_apply hint]
    rw [← integral_sub_left_eq_self _ volume z]
    simp only [sub_sub_cancel]
    rfl
  -- the reflected bump is a test function
  have hφd : ContDiff ℝ ∞ (fun y => ρ.normed volume (z - y)) :=
    hwd.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun y => ρ.normed volume (z - y)) := by
    have := hwc.comp_homeomorph (Homeomorph.subLeft z)
    simpa [Function.comp_def] using this
  have hφf : ∀ y v, fderiv ℝ (fun y => ρ.normed volume (z - y)) y v =
      -(fderiv ℝ (ρ.normed volume) (z - y) v) := by
    intro y v
    have h1 : HasFDerivAt (fun y : ℂ => z - y) (-ContinuousLinearMap.id ℝ ℂ) y :=
      (hasFDerivAt_id y).const_sub z
    have h2 : HasFDerivAt (fun y => ρ.normed volume (z - y))
        ((fderiv ℝ (ρ.normed volume) (z - y)).comp (-ContinuousLinearMap.id ℝ ℂ)) y :=
      ((hw1.differentiable one_ne_zero) (z - y)).hasFDerivAt.comp y h1
    rw [h2.fderiv]; simp
  obtain ⟨h1, hI⟩ := h _ hφd hφc (Set.subset_univ _)
  have key : ∀ (v : ℂ) (uv : ℂ → E),
      (∫ y, fderiv ℝ (fun y => ρ.normed volume (z - y)) y v • u y =
        -∫ y, ρ.normed volume (z - y) • uv y) →
        fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u) z v =
          (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] uv) z := by
    intro v uv hv
    rw [hderiv, convolution_eq_swap]
    simp only [hφf, neg_smul, integral_neg, neg_inj] at hv
    simpa using hv
  exact ⟨key 1 us h1, key Complex.I ut hI⟩

end JHolomorphic

open JHolomorphic

open MeasureTheory Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (ρ : ContDiffBump (0 : ℂ)) {u us ut : ℂ → E}
    (h : HasWeakPartialsOn Set.univ u us ut) (hu : LocallyIntegrable u volume) (z : ℂ) :
    fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u) z 1 =
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] us) z ∧
      fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u) z Complex.I =
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] ut) z :=
  JHolomorphic.fderiv_normed_convolution_eq_of_hasWeakPartialsOn_aux ρ h hu z
