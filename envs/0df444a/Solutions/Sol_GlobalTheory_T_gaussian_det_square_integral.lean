-- Prove2me | solution 1 for GlobalTheory.T.gaussian_det_square_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:10:52.479375+00:00
-- url     : https://prove2.me/submissions/4d1587e2-0487-4b8e-8160-1d8e00d06349

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegralStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_lintegral_gW_norm_det_sq


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
theorem _root_.solution : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (G : Matrix β (Fin d) ℂ), ∫⁻ C : Fin d → β → ℂ, gW d β C * ENNReal.ofReal (‖(Matrix.of C * G).det‖ ^ 2) = ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (G.conjTranspose * G).det.re) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq | exact GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.lintegral_gW_norm_det_sq <;> assumption)
end _root_.GlobalTheory.T
