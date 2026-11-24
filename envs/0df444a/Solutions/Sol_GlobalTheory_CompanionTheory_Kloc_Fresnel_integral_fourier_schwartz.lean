-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.integral_fourier_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:55.100799+00:00
-- url     : https://prove2.me/submissions/74d50d35-6a6a-4a76-be0f-412ed59b5692

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution (f : 𝓢(V, ℂ)) : ∫ w, 𝓕 (f : V → ℂ) w = f 0 := by
  have hint : Integrable (𝓕 (f : V → ℂ)) := by
    have := (𝓕 f).integrable (μ := volume)
    rwa [SchwartzMap.fourier_coe] at this
  have h := congrFun (Continuous.fourierInv_fourier_eq f.continuous (f.integrable (μ := volume)) hint) 0
  rw [Real.fourierInv_eq'] at h
  simpa using h
end GlobalTheory.CompanionTheory.Kloc.Fresnel
