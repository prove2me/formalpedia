-- Prove2me | solution 1 for GlobalTheory.GoodCharacterTail.tail_and_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:29.299399+00:00
-- url     : https://prove2.me/submissions/64a1c168-4110-401a-b059-6a4e46487f2a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2IntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TailAndSumBound
import Theorems.Thm_GlobalTheory_GoodCharacterTail_tail_le
import Theorems.Thm_GlobalTheory_GoodCharacterTail_eventually_log_le
import Theorems.Thm_GlobalTheory_T_gl2a2_integral_bound_of_sums


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open GlobalTheory GlobalTheory.GoodCharacterTail
open Formalism.HermitianLattices.GL2PrimeSums
namespace GlobalTheory.GoodCharacterTail
theorem _root_.solution : Formalism.HermitianLattices.GL2PrimeSums.TailSumBound := by
  intro ε hε hε1 C₁ c₁ CM hC₁ hc₁ hCM
  obtain ⟨C, c, hC, hc, hZ⟩ := GlobalTheory.T.gl2a2_integral_bound_of_sums C₁ c₁ hC₁ hc₁
  have e1 := eventually_log_le (1 / 400) (ε / 4) (by norm_num) (by linarith)
  have e2 := eventually_log_le c (ε / 6) hc (by linarith)
  have e3 := (tendsto_rpow_atTop (show 0 < ε / 2 by linarith)).eventually_ge_atTop (5 * C)
  have e4 := (tendsto_rpow_atTop (show 0 < ε / 6 by linarith)).eventually_ge_atTop 2
  have e5 := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have e6 := eventually_ge_atTop (2 : ℝ)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))
  refine ⟨x₀, 400 + CM + 1, ?_⟩
  intro x hx Q hQ hQ1 hQ2 a S hS hM H1 H2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hQ3 : 3 ≤ Q := by
    have h := Real.add_one_le_exp (Real.log Q)
    rw [Real.exp_log hQ] at h
    linarith
  have hz2 : 2 ≤ x ^ (400 : ℝ) := by
    have : x ^ (1 : ℝ) ≤ x ^ (400 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hlz : Real.log (x ^ (400 : ℝ)) = 400 * Real.log x := Real.log_rpow hx0 _
  have ht := tail_le a S hS (x ^ (400 : ℝ)) _ (by linarith)
    (fun U hU => hZ Q a hQ3 H1 H2 _ U hz2 hU)
  have hp : (x ^ (400 : ℝ)) ^ (-(1 : ℝ) / 400) = x⁻¹ := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_neg_one]
    norm_num
  have hl : Real.log (x ^ (400 : ℝ) * Q) = 400 * Real.log x + Real.log Q := by
    rw [Real.log_mul (by positivity) hQ.ne', hlz]
  rw [hp, hl] at ht
  have hsq : x ^ (ε / 4) * x ^ (ε / 4) = x ^ (ε / 2) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hsq2 : x ^ (ε / 2) * x ^ (ε / 2) = x ^ ε := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hL : (400 * Real.log x + Real.log Q) ^ 2 ≤ 4 * x ^ (ε / 2) := by
    have a1 : 0 ≤ 400 * Real.log x + Real.log Q := by linarith
    have a2 : 400 * Real.log x + Real.log Q ≤ 2 * x ^ (ε / 4) := by linarith
    have := pow_le_pow_left₀ a1 a2 2
    nlinarith
  have hQc : x * Q ^ (-c) ≤ 1 := by
    rw [Real.rpow_def_of_pos hQ]
    nth_rewrite 1 [← Real.exp_log hx0]
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have := mul_le_mul_of_nonneg_left hQ1 hc.le
    linarith
  have h1e : 1 ≤ x ^ (ε / 2) := Real.one_le_rpow hx1 (by linarith)
  have key : x * ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ x ^ ε := by
    have b1 := mul_le_mul_of_nonneg_left ht hx0.le
    have b2 : x * (C * (x⁻¹ * (400 * Real.log x + Real.log Q) ^ 2 + Q ^ (-c))) =
        C * ((400 * Real.log x + Real.log Q) ^ 2 + x * Q ^ (-c)) := by
      field_simp
    rw [b2] at b1
    have b3 : C * ((400 * Real.log x + Real.log Q) ^ 2 + x * Q ^ (-c)) ≤ C * (5 * x ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    have b4 : 5 * C * x ^ (ε / 2) ≤ x ^ (ε / 2) * x ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right f3 (by linarith)
    linarith
  refine ⟨?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    exact key
  · have c1 : x ^ ε ≤ x := by
      have : x ^ ε ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hε1.le
      rwa [Real.rpow_one] at this
    have c2 : ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ 1 := by
      have : x * ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ x * 1 := by linarith
      exact le_of_mul_le_mul_left this hx0
    have c3 : ‖∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ 400 * Real.log x + CM := by
      rw [← hlz]
      refine le_trans ((norm_sum_le _ _).trans (le_of_eq ?_)) (hM _ (by linarith))
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [norm_div, Complex.norm_natCast]
    have c4 := norm_add_le (S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))
      (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))
    rw [sub_add_cancel] at c4
    nlinarith
end GlobalTheory.GoodCharacterTail
