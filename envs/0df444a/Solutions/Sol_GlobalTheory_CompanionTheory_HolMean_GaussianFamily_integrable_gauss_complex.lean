-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.GaussianFamily.integrable_gauss_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:15.128073+00:00
-- url     : https://prove2.me/submissions/0fc48779-e6fc-4b42-a70a-8c2946b7a20e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HolomorphicParameterIntegralGaussianBound

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
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun w : ℂ => Real.exp (-δ * ‖w‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ)
    (b := (δ : ℂ)) (by simpa using hδ) 0 0
  have h2 := h.norm
  refine h2.congr (ae_of_all _ fun w => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  have : (-(δ : ℂ) * ((‖w‖ : ℝ) : ℂ) ^ 2) = ((-δ * ‖w‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]
end GlobalTheory.CompanionTheory.HolMean.GaussianFamily
