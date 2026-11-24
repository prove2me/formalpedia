-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.pM_mul_rM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:47:10.261514+00:00
-- url     : https://prove2.me/submissions/8ea1cf34-c973-41f8-aafa-ab26f2fc8bd4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_rk_mul_rk
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_one_add_mul_one_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_sqrt_facts

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
theorem _root_.solution (f : β → ℂ) : pM f * rM f = 1 := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  unfold pM rM
  rw [one_add_mul_one_sub _ _ _ _ (rk_mul_rk f)]
  have : ((1 / (1 + √(nS f)) : ℝ) : ℂ) - ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) -
      ((1 / (1 + √(nS f)) : ℝ) : ℂ) * ((1 / (√(nS f) * (1 + √(nS f))) : ℝ) : ℂ) *
        ((nS f - 1 : ℝ) : ℂ) = 0 := by
    norm_cast
    generalize √(nS f) = s at h0 h1 ⊢
    rw [← h1]
    field_simp
    ring
  rw [this, zero_smul, add_zero]
end GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
