-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.integrable_gauss_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:13.0908+00:00
-- url     : https://prove2.me/submissions/a2b83d9d-56b8-4afc-891c-c742789d078a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivIntegralGaussianExponential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
namespace GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
theorem _root_.solution :
    Integrable (fun w : ℂ => Real.exp (-Real.pi * ‖w‖ ^ 2)) := by
  have hb : 0 < ((Real.pi : ℂ)).re := by simpa using Real.pi_pos
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0).norm
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, zero_mul, add_zero, Complex.norm_exp]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
