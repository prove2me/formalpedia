-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integrable_sq_exp_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:30:05.049356+00:00
-- url     : https://prove2.me/submissions/890ef14e-30ec-493d-9208-5b7cbfda9487

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integral_sq_exp_sq

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.GaussDet
namespace GlobalTheory.CompanionTheory.FSCrofton.GaussDet
theorem _root_.solution : Integrable (fun z : ℂ => ‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) :=
  Integrable.of_integral_ne_zero (by rw [integral_sq_exp_sq]; exact Real.pi_ne_zero)
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
