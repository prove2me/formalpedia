-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.GaussianFamily.integrable_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:15.101535+00:00
-- url     : https://prove2.me/submissions/3c3ebfd8-74ea-48ab-ae69-e4cf267c98fb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HolomorphicParameterIntegralGaussianBound
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_GaussianFamily_integrable_gauss_complex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean GlobalTheory.CompanionTheory.HolMean.GaussianFamily
namespace GlobalTheory.CompanionTheory.HolMean.GaussianFamily
theorem _root_.solution (m n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun v : Fin m → Fin n → ℂ => Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) := by
  have h1 : Integrable (fun u : Fin n → ℂ => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2))
      (volume : Measure (Fin n → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℂ))
      (f := fun _ (w : ℂ) => Real.exp (-δ * ‖w‖ ^ 2)) fun _ => integrable_gauss_complex hδ
    exact this
  have h2 : Integrable (fun v : Fin m → Fin n → ℂ => ∏ a, ∏ j, Real.exp (-δ * ‖v a j‖ ^ 2))
      (volume : Measure (Fin m → Fin n → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : Fin m => (volume : Measure (Fin n → ℂ)))
      (f := fun _ (u : Fin n → ℂ) => ∏ j, Real.exp (-δ * ‖u j‖ ^ 2)) fun _ => h1
    exact this
  refine h2.congr (ae_of_all _ fun v => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum]
end GlobalTheory.CompanionTheory.HolMean.GaussianFamily
