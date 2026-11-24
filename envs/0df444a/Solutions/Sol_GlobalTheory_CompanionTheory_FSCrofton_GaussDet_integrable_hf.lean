-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integrable_hf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:47:12.74894+00:00
-- url     : https://prove2.me/submissions/15f65597-ebf9-434d-916c-5da67f076333

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integrable_exp_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integrable_sq_exp_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_continuous_hf

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
theorem _root_.solution (p q : Prop) [Decidable p] [Decidable q] : Integrable (hf p q) := by
  refine Integrable.mono' (integrable_exp_sq.add integrable_sq_exp_sq)
    (continuous_hf p q).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  have he : 0 < Real.exp (-‖z‖ ^ 2) := Real.exp_pos _
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hn : ‖((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ = Real.exp (-‖z‖ ^ 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hb : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  simp only [hf, norm_mul, hn, Pi.add_apply]
  by_cases hp : p <;> by_cases hq : q <;> simp only [hp, hq, if_true, if_false, norm_one, Complex.norm_conj] <;>
    nlinarith [mul_le_mul_of_nonneg_right hb he.le, mul_pos he he, mul_nonneg (sq_nonneg ‖z‖) he.le]
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
