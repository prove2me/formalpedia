-- Prove2me | solution 1 for GlobalTheory.T.continuous_isBigO_rpow_lipschitzProductKernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:24.34591+00:00
-- url     : https://prove2.me/submissions/8f3e8ca7-caa2-453a-bb99-44c9c615ebf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernelStatement
import Theorems.Thm_GlobalTheory_LipschitzTR_continuous_and_isBigO_rpow_Phi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Continuous (Phi k z) ∧ ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := by
  first | exact @GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi | exact GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi | (intros; apply GlobalTheory.LipschitzTR.continuous_and_isBigO_rpow_Phi <;> assumption)
end _root_.GlobalTheory.T
