-- Prove2me | solution 1 for GlobalTheory.T.gamma_integral_exp_substitution_real_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:10:34.728288+00:00
-- url     : https://prove2.me/submissions/26cf642b-8162-4486-a9ec-f8f677216ed9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLine
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLineStatement
import Theorems.Thm_GlobalTheory_HeckeMellin_gamma_integral_exp_substitution


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (r : ℝ), 0 < r → ∀ w : ℂ, 0 < w.re → Integrable (fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))) ∧ ∫ t : ℝ, Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ)) = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) := by
  first | exact @GlobalTheory.HeckeMellin.gamma_integral_exp_substitution | exact GlobalTheory.HeckeMellin.gamma_integral_exp_substitution | (intros; apply GlobalTheory.HeckeMellin.gamma_integral_exp_substitution <;> assumption)
end _root_.GlobalTheory.T
