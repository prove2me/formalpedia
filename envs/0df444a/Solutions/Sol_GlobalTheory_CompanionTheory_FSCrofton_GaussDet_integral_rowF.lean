-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integral_rowF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:20:11.461716+00:00
-- url     : https://prove2.me/submissions/8ceada11-c80e-4b9a-b42e-ed8adf24f5bd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integrable_row
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integral_row
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_rowF_eq

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
theorem _root_.solution (G : Matrix β (Fin d) ℂ) (a c : Fin d) :
    ∫ r, rowF G a c r = (Real.pi : ℂ) ^ Fintype.card β * (G.conjTranspose * G) c a := by
  simp_rw [rowF_eq]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
    (integrable_row i j).const_mul _]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (integrable_row i j).const_mul _]
  simp only [integral_const_mul, integral_row, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  simp only [Complex.star_def]
  ring
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
