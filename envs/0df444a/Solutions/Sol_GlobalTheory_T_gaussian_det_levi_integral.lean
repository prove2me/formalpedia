-- Prove2me | solution 1 for GlobalTheory.T.gaussian_det_levi_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:38:48.601797+00:00
-- url     : https://prove2.me/submissions/3b6e3e47-1b97-4d20-a0d8-7afa8a8a5e7e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegralStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_lintegral_gauss_levi


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
theorem _root_.solution : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (f : β → ℂ) (F : Matrix β (Fin d) ℂ), ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (fsLevi f F).det.re) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi | exact GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi <;> assumption)
end _root_.GlobalTheory.T
