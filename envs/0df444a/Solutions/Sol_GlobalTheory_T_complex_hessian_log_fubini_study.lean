-- Prove2me | solution 1 for GlobalTheory.T.complex_hessian_log_fubini_study
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:36.257732+00:00
-- url     : https://prove2.me/submissions/f8e8f9c7-effe-4f46-83fe-51e8094e4901

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudy
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudyStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_cHess_log_one_add_sum
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
theorem _root_.solution : ∀ (d : ℕ) (β : Type) [Fintype β] (U : Set (V d)) (f : β → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → ∀ z ∈ U, cHess d (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) z = fsLevi (fun j => f j z) (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum | exact GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.cHess_log_one_add_sum <;> assumption)
end _root_.GlobalTheory.T
