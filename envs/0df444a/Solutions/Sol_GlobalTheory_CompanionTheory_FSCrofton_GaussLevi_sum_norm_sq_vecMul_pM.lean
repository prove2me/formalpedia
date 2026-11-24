-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.sum_norm_sq_vecMul_pM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:47:13.421819+00:00
-- url     : https://prove2.me/submissions/d3b2b9f0-6bda-4691-af81-bdd5cb22163b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_sqrt_facts
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_vecMul_pM_apply

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
theorem _root_.solution (f r : β → ℂ) :
    ∑ j, ‖(r ᵥ* pM f) j‖ ^ 2 = ‖∑ i, r i * f i‖ ^ 2 + ∑ j, ‖r j‖ ^ 2 := by
  obtain ⟨h0, h1⟩ := sqrt_facts f
  have ht1 : (1 / (1 + √(nS f))) ^ 2 * (nS f - 1) + 2 * (1 / (1 + √(nS f))) = 1 := by
    generalize √(nS f) = s at h0 h1 ⊢
    rw [← h1]
    field_simp
    ring
  generalize ha : ∑ i, r i * f i = a
  generalize htt : 1 / (1 + √(nS f)) = t at ht1
  have hterm : ∀ j, ‖(r ᵥ* pM f) j‖ ^ 2 =
      ‖r j‖ ^ 2 + t ^ 2 * ‖a‖ ^ 2 * ‖f j‖ ^ 2 + 2 * t * (r j * f j * conj a).re := by
    intro j
    rw [vecMul_pM_apply, ha, htt, Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm (r j)]
    have e1 : Complex.normSq ((t : ℂ) * a * conj (f j)) = t ^ 2 * ‖a‖ ^ 2 * ‖f j‖ ^ 2 := by
      simp [Complex.normSq_eq_norm_sq, mul_pow]
    have e2 : r j * conj ((t : ℂ) * a * conj (f j)) = (t : ℂ) * (r j * f j * conj a) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [e1, e2, Complex.re_ofReal_mul]
    ring
  have hs : ∑ j, (r j * f j * conj a).re = ‖a‖ ^ 2 := by
    rw [← Complex.re_sum, ← Finset.sum_mul, ha, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hf : ∑ j, ‖f j‖ ^ 2 = nS f - 1 := by simp [nS]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, hf]
  linear_combination ‖a‖ ^ 2 * ht1
end GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
