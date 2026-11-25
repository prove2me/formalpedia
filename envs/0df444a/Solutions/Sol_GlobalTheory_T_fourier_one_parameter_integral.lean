-- Prove2me | solution 1 for GlobalTheory.T.fourier_one_parameter_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:39.235158+00:00
-- url     : https://prove2.me/submissions/5ea9e61a-2807-4dac-b8bf-acfb5bd83f0b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegral
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegralStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_OneParamFourier_integral_mul_char_eq_of_hasDerivAt


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
theorem _root_.solution : ∀ (A : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A), Continuous c → ∀ (F G : A → ℂ), Continuous F → Continuous G → Integrable F lam → Integrable G lam → ∀ (χ : AddChar A ℂ), Continuous χ → (∀ x, ‖χ x‖ = 1) → ∀ (f : ℝ), (∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ)))) → (∀ (b : A) (s : ℝ), HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) → ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt | exact GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt | (intros; apply GlobalTheory.CompanionTheory.OneParamFourier.integral_mul_char_eq_of_hasDerivAt <;> assumption)
end _root_.GlobalTheory.T
