-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integral_fR_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:57:22.242568+00:00
-- url     : https://prove2.me/submissions/da852e10-83c1-4f97-a4f5-542b4e97ebdd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_det_expand
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_perm_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integrable_prod_rowF
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integral_prod_rowF

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
    ∫ C, ((fR G C : ℝ) : ℂ) = ((Real.pi : ℂ) ^ Fintype.card β) ^ d * (d.factorial : ℂ) *
      (G.conjTranspose * G).det := by
  simp_rw [fR, det_expand]
  rw [integral_finset_sum _ fun σ _ => integrable_finset_sum _ fun τ _ =>
    (integrable_prod_rowF G σ τ).const_mul _]
  rw [← perm_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finset_sum _ fun τ _ => (integrable_prod_rowF G σ τ).const_mul _]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_prod_rowF]
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
