-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.fourierInvCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:28.021901+00:00
-- url     : https://prove2.me/submissions/47836563-6e76-45d0-9995-e8609cf34277

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionFiniteDim
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_inner_eq_sum_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
universe u
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (g : (ι → ℝ) → ℂ), Continuous g → MeasureTheory.Integrable g →
    MeasureTheory.Integrable (fun t : ι → ℝ =>
      ∫ y, g y * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) →
    ∀ y : ι → ℝ, (∫ t : ι → ℝ, (∫ y', g y' * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y' i : ℂ) * t i)) *
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i)) = g y := by
  intro ι _ g hgc hgi hFi y
  set F : (ι → ℝ) → ℂ := fun t =>
    ∫ y, g y * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i) with hF
  let f : EuclideanSpace ℝ ι → ℂ := fun v => g (WithLp.ofLp v)
  have mp := PiLp.volume_preserving_ofLp ι
  have memb : MeasurableEmbedding (@WithLp.ofLp 2 (ι → ℝ)) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurableEmbedding
  have hfc : Continuous f := hgc.comp (PiLp.continuous_ofLp 2 _)
  have hfi : Integrable f := (mp.integrable_comp hgi.aestronglyMeasurable).2 hgi
  have hFou : ∀ v : EuclideanSpace ℝ ι, 𝓕 f v = F (WithLp.ofLp v) := by
    intro v
    rw [Real.fourier_eq']
    simp only [hF]
    rw [← mp.integral_comp memb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [smul_eq_mul, f]
    rw [mul_comm]
    congr 2
    rw [inner_eq_sum_coord]
    push_cast
    ring
  have hFfun : 𝓕 f = fun v => F (WithLp.ofLp v) := funext hFou
  have hFi' : Integrable (𝓕 f) := by
    rw [hFfun]
    exact (mp.integrable_comp hFi.aestronglyMeasurable).2 hFi
  have hinv : 𝓕⁻ (𝓕 f) = f := Continuous.fourierInv_fourier_eq hfc hfi hFi'
  have h := congrFun hinv (WithLp.toLp 2 y)
  rw [Real.fourierInv_eq', hFfun] at h
  have h2 : ∫ t : ι → ℝ, F t * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i) =
      ∫ v : EuclideanSpace ℝ ι, Complex.exp (((2 * Real.pi * ⟪v, WithLp.toLp 2 y⟫ : ℝ) : ℂ) * Complex.I) •
        F (WithLp.ofLp v) := by
    rw [← mp.integral_comp memb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    rw [inner_eq_sum_coord]
    push_cast
    simp only [mul_comm]
    ring
  exact h2.trans h
end GlobalTheory.CompanionTheory.EisTube
