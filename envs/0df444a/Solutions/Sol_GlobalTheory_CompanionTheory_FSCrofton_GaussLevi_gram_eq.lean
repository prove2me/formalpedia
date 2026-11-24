-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:03:27.855089+00:00
-- url     : https://prove2.me/submissions/9df0e9ff-7fa7-476e-9d93-497473bd1165

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_rM_conjTranspose
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_rM_mul_rM

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
open Matrix
variable {β : Type} [Fintype β] [DecidableEq β]
namespace GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
theorem _root_.solution {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    (rM f * F)ᴴ * (rM f * F) =
      Fᴴ * F - ((1 / nS f : ℝ) : ℂ) • vecMulVec (Fᴴ *ᵥ f) (star f ᵥ* F) := by
  rw [conjTranspose_mul, rM_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (rM f), rM_mul_rM,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]
  congr 2
  unfold rk
  rw [vecMulVec_mul, mul_vecMulVec]
end GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
