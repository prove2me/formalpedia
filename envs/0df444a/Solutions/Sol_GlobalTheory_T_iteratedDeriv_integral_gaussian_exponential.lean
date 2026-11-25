-- Prove2me | solution 1 for GlobalTheory.T.iteratedDeriv_integral_gaussian_exponential
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:45.932403+00:00
-- url     : https://prove2.me/submissions/79a43410-02a9-4250-8b14-29a82e050259

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivIntegralGaussianExponential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivIntegralGaussianExponentialStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_DilatedGaussian_holomorphic_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (m n : ℕ) (X : Fin n → ℝ) (K : (Fin m → Fin n → ℂ) → ℂ), Continuous K → (∀ v, ‖K v‖ ≤ 1) → ∃ ρ : ℝ, 0 < ρ ∧ DifferentiableOn ℂ (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) (Metric.ball 0 ρ) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => ∫ v, K v * (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = ∫ v, K v * iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 := by
  first | exact @GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.holomorphic_integral | exact GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.holomorphic_integral | (intros; apply GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.holomorphic_integral <;> assumption)
end _root_.GlobalTheory.T
