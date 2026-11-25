-- Prove2me | solution 1 for GlobalTheory.T.fourier_parameter_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:19:41.349087+00:00
-- url     : https://prove2.me/submissions/ab4666a2-60ca-4323-b5e3-400d508c1585

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierParameterDerivative
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierParameterDerivativeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Analysis_OscPhase_hasDerivAt_integral_oscillating_phase


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
theorem _root_.solution : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (g : X → ℂ) (M : X → ℝ), Measurable M → Integrable g μ → Integrable (fun y => (M y : ℂ) * g y) μ → ∀ s : ℝ, HasDerivAt (fun t : ℝ => ∫ y, g y * Complex.exp (2 * Real.pi * Complex.I * ((t * M y : ℝ) : ℂ)) ∂μ) (2 * Real.pi * Complex.I * ∫ y, (M y : ℂ) * g y * Complex.exp (2 * Real.pi * Complex.I * ((s * M y : ℝ) : ℂ)) ∂μ) s := by
  first | exact @GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase | exact GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase | (intros; apply GlobalTheory.CompanionTheory.Analysis.OscPhase.hasDerivAt_integral_oscillating_phase <;> assumption)
end _root_.GlobalTheory.T
