-- Prove2me | solution 1 for MasulloRH.lifted_rank_one_schatten_norms
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:21:14.520609+00:00
-- url     : https://prove2.me/submissions/5255a63c-6507-4ad0-9421-7f93e1a7a0e4

import Definitions.Def_MasulloGRH_HilbertNuclear

open MasulloGRH InnerProductSpace
open scoped ComplexConjugate

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (x y : H) :
    traceNorm (rankOne ℂ x y) = ‖x‖ * ‖y‖ ∧
      hilbertSchmidtNorm (rankOne ℂ x y) = ‖x‖ * ‖y‖ := by
  classical
  let b := chosenHilbertBasis H
  have parseval := (b.hasSum_inner_mul_inner y y).mapL Complex.reCLM
  have hcoeff : HasSum (fun i => ‖inner ℂ y (b i)‖ ^ 2) (‖y‖ ^ 2) := by
    convert parseval using 1
    · funext i
      change _ = (inner ℂ y (b i) * inner ℂ (b i) y).re
      rw [← inner_conj_symm (𝕜 := ℂ) (b i) y]
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    · simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  constructor
  · by_cases hy : y = 0
    · subst y
      simp [traceNorm, operatorTrace, operatorAbs, rankOne_def]
    have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    let c := ‖x‖ / ‖y‖
    let B := c • rankOne ℂ y y
    have hB : 0 ≤ B := smul_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))
      ((ContinuousLinearMap.nonneg_iff_isPositive _).2 (isPositive_rankOne_self _))
    have hsquare : star (rankOne ℂ x y) * rankOne ℂ x y = B * B := by
      rw [ContinuousLinearMap.star_eq_adjoint, adjoint_rankOne]
      simp only [B, smul_mul_assoc, mul_smul_comm, ContinuousLinearMap.mul_def,
        rankOne_comp_rankOne, inner_self_eq_norm_sq_to_K]
      simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      congr 1
      simp [c]
      field_simp [show (‖y‖ : ℂ) ≠ 0 by exact_mod_cast hny]
    rw [traceNorm, operatorAbs, hsquare, CFC.sqrt_mul_self B hB]
    have htrace : operatorTrace B = (c : ℂ) * inner ℂ y y := by
      unfold operatorTrace
      rw [← ((b.hasSum_inner_mul_inner y y).mul_left (c : ℂ)).tsum_eq]
      apply tsum_congr
      intro i
      change inner ℂ (b i) (c • (inner ℂ y (b i) • y)) = _
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c, inner_smul_right, inner_smul_right]
      rfl
    rw [htrace, inner_self_eq_norm_sq_to_K]
    simp [c, ← Complex.ofReal_pow]
    field_simp
  · unfold hilbertSchmidtNorm
    simp only [rankOne_apply, norm_smul, mul_pow]
    rw [(hcoeff.mul_right (‖x‖ ^ 2)).tsum_eq, ← mul_pow,
      Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_comm]
