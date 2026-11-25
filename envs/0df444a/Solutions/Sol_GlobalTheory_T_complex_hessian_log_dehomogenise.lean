-- Prove2me | solution 1 for GlobalTheory.T.complex_hessian_log_dehomogenise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:54:24.630515+00:00
-- url     : https://prove2.me/submissions/e1a5099d-a1b1-4acc-bcde-968af4e6ec25

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogenise
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogeniseStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_HessFrame_cHess_log_sum_normSq_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → ∀ z ∈ U, cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z = cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ)) z := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq | exact GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq <;> assumption)
end _root_.GlobalTheory.T
