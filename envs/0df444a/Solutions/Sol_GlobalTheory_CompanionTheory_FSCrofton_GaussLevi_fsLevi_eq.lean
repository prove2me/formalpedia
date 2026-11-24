-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.fsLevi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:20:12.17183+00:00
-- url     : https://prove2.me/submissions/40786ead-c8ff-4e56-8ff9-334763c52521

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_nS_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_gram_eq

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
    fsLevi f F = ((1 / nS f : ℝ) : ℂ) • ((rM f * F)ᴴ * (rM f * F))ᵀ := by
  have hS : ((nS f : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (nS_pos f).ne'
  rw [gram_eq]
  ext a c
  have hX : ∑ j, F j a * conj (F j c) = (Fᴴ * F) c a := by
    simp [Matrix.mul_apply, mul_comm]
  have hY : ∑ j, F j a * conj (f j) = (star f ᵥ* F) a := by
    simp [vecMul, dotProduct, mul_comm]
  have hZ : ∑ j, f j * conj (F j c) = (Fᴴ *ᵥ f) c := by
    simp [mulVec, dotProduct, mul_comm]
  have h1 : ((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) = ((nS f : ℝ) : ℂ) := rfl
  simp only [fsLevi, of_apply, hX, hY, hZ, h1, Matrix.smul_apply, transpose_apply, Matrix.sub_apply,
    vecMulVec_apply, smul_eq_mul]
  push_cast
  field_simp
end GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
