-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integrable_fR_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:57:21.375131+00:00
-- url     : https://prove2.me/submissions/6927a353-2e7b-4a64-95cd-03517c7aa046

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_det_expand
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integrable_prod_rowF

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
variable {β : Type} [Fintype β] [DecidableEq β]
variable {d : ℕ}
namespace GlobalTheory.CompanionTheory.FSCrofton.GaussDet
theorem _root_.solution (G : Matrix β (Fin d) ℂ) :
    Integrable (fun C => ((fR G C : ℝ) : ℂ)) := by
  simp_rw [fR, det_expand]
  exact integrable_finset_sum _ fun σ _ => integrable_finset_sum _ fun τ _ =>
    (integrable_prod_rowF G σ τ).const_mul _
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
