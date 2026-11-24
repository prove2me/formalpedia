-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussDet.integral_hf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:46:57.957658+00:00
-- url     : https://prove2.me/submissions/b1f737a2-e836-4bb9-8ebe-91172de54cd5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integral_exp_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_integral_sq_exp_sq
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussDet_hf_neg_of_ne

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
theorem _root_.solution (p q : Prop) [Decidable p] [Decidable q] :
    ∫ z, hf p q z = if p ↔ q then (Real.pi : ℂ) else 0 := by
  by_cases h : p ↔ q
  · rw [if_pos h]
    by_cases hp : p
    · have hq : q := h.1 hp
      have : hf p q = fun z : ℂ => ((‖z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
        funext z
        simp only [hf, hp, hq, if_true, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        ring
      simp_rw [this]
      rw [integral_complex_ofReal, integral_sq_exp_sq]
    · have hq : ¬ q := fun hq => hp (h.2 hq)
      have : hf p q = fun z : ℂ => ((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) := by
        funext z
        simp only [hf, hp, hq, if_false, one_mul]
      simp_rw [this]
      rw [integral_complex_ofReal, integral_exp_sq]
  · rw [if_neg h]
    have h1 : ∫ z, hf p q (-z) = ∫ z, hf p q z := integral_neg_eq_self _ _
    simp only [hf_neg_of_ne p q h, integral_neg] at h1
    have h2 : (2 : ℂ) * ∫ z, hf p q z = 0 := by linear_combination -h1
    simpa using h2
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet
