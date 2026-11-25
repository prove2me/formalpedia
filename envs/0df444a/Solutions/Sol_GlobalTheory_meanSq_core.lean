-- Prove2me | solution 1 for GlobalTheory.meanSq_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:05.004471+00:00
-- url     : https://prove2.me/submissions/451b839e-25d4-42f9-91a6-cd55200743f8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimePowerVonMangoldtSumBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqIocLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumVonMangoldtDivSqTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumDivSubLeTwoLogOfPartialSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MeanSqCardPrimeFactorsOutPart
import Theorems.Thm_GlobalTheory_meanSq_cn_nonneg
import Theorems.Thm_GlobalTheory_meanSq_expand
import Theorems.Thm_GlobalTheory_meanSq_abs_mean_le_one
import Theorems.Thm_GlobalTheory_meanSq_pairs
import Theorems.Thm_GlobalTheory_chebyshev_coefficient_sum_bound
import Theorems.Thm_GlobalTheory_prime_power_von_mangoldt_sum_bound
import Theorems.Thm_GlobalTheory_prime_sum_square_bound
import Theorems.Thm_GlobalTheory_remainder_smooth_rough_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2
namespace GlobalTheory
theorem _root_.solution : Formalism.HermitianLattices.GL2PrimeSums.JacobiTwistedMeanSquareBound := by
  intro hψ ε hε hε1 C' c' hC' hc'
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.chebyshev_coefficient_sum_bound hψ
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.prime_sum_square_bound hψ
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.remainder_smooth_rough_bound hψ
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.prime_power_von_mangoldt_sum_bound
  refine ⟨max (Real.exp 1) (Real.exp (2 / c')), C' * C₁ ^ 2 + C₂ + (5 * |C₃| + 4 * |C₄|) ^ 2, ?_⟩
  intro x hx m₀ PPs κ nStar _ hm₀ hpr _ _ _ _ hκ hμ
  have hxe : Real.exp 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ x := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hL2 : 2 / c' ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 ((le_max_right _ _).trans hx)
  have hL0 : 0 ≤ Real.log x := by linarith
  have h1 := meanSq_expand (Icc 1 ⌊x ^ (400 : ℝ)⌋₊) PPs (cn x) (meanSq_cn_nonneg hx0.le) κ hκ
  have h2 := meanSq_pairs hx0.le m₀ hm₀ nStar
    (fun n n' => |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card|)
    (C' * Real.exp (-c' * Real.log x ^ 2)) (|C₄| * Real.log x) (by positivity) (by positivity)
    (fun p hp => (hC₄ x hx2 p hp).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hL0))
    (fun n n' => meanSq_abs_mean_le_one PPs _) hμ
  unfold sqSum
  refine (h1.trans h2).trans ?_
  have e1 : C' * Real.exp (-c' * Real.log x ^ 2) * (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n) ^ 2 ≤
      C' * C₁ ^ 2 * x * Real.log x := by
    have s1 : (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n) ^ 2 ≤ (C₁ * x * Real.log x) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => meanSq_cn_nonneg hx0.le n) (hC₁ x hx2) 2
    have s2 : Real.exp (-c' * Real.log x ^ 2) * (x * Real.log x) ≤ 1 := by
      have t1 : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
      have t2 : 2 ≤ c' * Real.log x := by rw [div_le_iff₀ hc'] at hL2; linarith
      have t3 : x * x = Real.exp (2 * Real.log x) := by
        rw [two_mul, Real.exp_add, Real.exp_log hx0]
      calc Real.exp (-c' * Real.log x ^ 2) * (x * Real.log x)
          ≤ Real.exp (-c' * Real.log x ^ 2) * (x * x) := by gcongr
        _ = Real.exp (-c' * Real.log x ^ 2 + 2 * Real.log x) := by rw [t3, Real.exp_add]
        _ ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith [mul_le_mul_of_nonneg_right t2 hL0]
    calc _ ≤ C' * Real.exp (-c' * Real.log x ^ 2) * (C₁ * x * Real.log x) ^ 2 := by gcongr
      _ = (C' * C₁ ^ 2 * x * Real.log x) * (Real.exp (-c' * Real.log x ^ 2) * (x * Real.log x)) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) s2
  have e2 := hC₂ x hx2
  have e3 : (Rsum x m₀ + 2 * (|C₄| * Real.log x)) ^ 2 ≤ (5 * |C₃| + 4 * |C₄|) ^ 2 * x * Real.log x := by
    have r0 : 0 ≤ Rsum x m₀ := by
      unfold Rsum sP
      exact add_nonneg (Finset.sum_nonneg fun n _ => meanSq_cn_nonneg hx0.le n)
        (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun i _ => meanSq_cn_nonneg hx0.le _)
    have r1 := hC₃ ε hε hε1 x hx2 m₀ hm₀ hpr
    have r2 : Real.log x ≤ x ^ ((1 : ℝ) / 2) / (1 / 2) := Real.log_le_rpow_div hx0.le (by norm_num)
    have r3 : Real.log x ≤ x ^ ((1 : ℝ) / 4) / (1 / 4) := Real.log_le_rpow_div hx0.le (by norm_num)
    have r4 : x ^ (ε / 5) ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have r5 : x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 4) = x ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hx0]; norm_num
    have r6 : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
      rw [sq, ← Real.rpow_add hx0]; norm_num
    have r7 : x ^ (ε / 5) * Real.log x ≤ 4 * x ^ ((1 : ℝ) / 2) := by
      have := mul_le_mul r4 r3 hL0 (by positivity)
      rw [← r5]; linarith
    have r8 : Rsum x m₀ ≤ |C₃| * (5 * x ^ ((1 : ℝ) / 2)) := by
      refine r1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_)
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have r9 : |C₄| * Real.log x ≤ |C₄| * (2 * x ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    calc _ ≤ ((5 * |C₃| + 4 * |C₄|) * x ^ ((1 : ℝ) / 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = (5 * |C₃| + 4 * |C₄|) ^ 2 * x := by rw [mul_pow, r6]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hL1
  linarith
end GlobalTheory
