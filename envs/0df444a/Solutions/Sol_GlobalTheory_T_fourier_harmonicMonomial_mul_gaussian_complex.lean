-- Prove2me | solution 1 for GlobalTheory.T.fourier_harmonicMonomial_mul_gaussian_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:09:35.843493+00:00
-- url     : https://prove2.me/submissions/8589f111-9124-477d-b96c-f1743902d53b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHarmonicMonomialMulGaussianComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierHarmonicMonomialMulGaussianComplexStatement
import Theorems.Thm_GlobalTheory_HeckeLemma_fourier_hmon_mul_gaussian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : ℤ) (l : ℂ), 𝓕 (fun w : ℂ => GlobalTheory.HeckeTheta.hmon k w * Complex.exp ((-2 * Real.pi * ‖w‖ ^ 2 : ℝ) : ℂ)) l = (1 / 2 : ℂ) * (-Complex.I) ^ k.natAbs * (GlobalTheory.HeckeTheta.hmon k (l / 2) * Complex.exp ((-2 * Real.pi * ‖l / 2‖ ^ 2 : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian | exact GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian | (intros; apply GlobalTheory.HeckeLemma.fourier_hmon_mul_gaussian <;> assumption)
end _root_.GlobalTheory.T
