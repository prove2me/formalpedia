-- Prove2me | solution 1 for GlobalTheory.HeckeMellin.exp_smul_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:19:05.709689+00:00
-- url     : https://prove2.me/submissions/ece5e09b-4aca-40d1-987f-9eecfd007119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellin
open Set
namespace GlobalTheory.HeckeMellin
theorem _root_.solution (w : ℂ) (c t : ℝ) :
    |Real.exp t| • (((Real.exp t : ℝ) : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * (Real.exp t : ℝ)))) =
      Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by
  rw [abs_of_pos (Real.exp_pos t), Complex.real_smul]
  have hne : ((Real.exp t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  rw [Complex.ofReal_exp]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring
end GlobalTheory.HeckeMellin
