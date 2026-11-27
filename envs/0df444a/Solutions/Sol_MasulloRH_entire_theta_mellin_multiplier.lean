-- Prove2me | solution 1 for MasulloRH.entire_theta_mellin_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:26:45.909742+00:00
-- url     : https://prove2.me/submissions/e5f678c9-bcb2-4c20-9aeb-941c6effd2e0

import Definitions.Def_MasulloRH_RationalThetaGrid
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MasulloRH.RationalThetaGrid Set Filter
open scoped Topology

private lemma hL : logTwo ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
private lemma cp (s : ℂ) : (2:ℂ)^s = Complex.exp (logTwo*s) := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  simp [logTwo, Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]

theorem solution :
    Differentiable ℂ thetaMultiplier ∧
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      thetaMultiplier s = (1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))*completedRiemannZeta s) ∧
    thetaMultiplier 1 = logTwo/2 := by
  have hsl : Differentiable ℂ (dslope Complex.exp 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (Filter.univ_mem : (univ:Set ℂ)∈𝓝 0)).2
      Complex.differentiable_exp.differentiableOn)
  have hZeta : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  refine ⟨?_,?_,?_⟩
  · unfold thetaMultiplier regZ
    fun_prop (disch := first | exact hsl | exact differentiable_completedZeta₀)
  · intro s hs ho
    have he := sub_smul_dslope Complex.exp 0 (-logTwo*s)
    have hf := sub_smul_dslope Complex.exp 0 (logTwo*(1-s))
    simp only [sub_zero,smul_eq_mul,Complex.exp_zero] at he hf
    have hZ : regZ s = s*(1-s)*completedRiemannZeta s := by
      rw [completedRiemannZeta_eq];unfold regZ
      field_simp [hs,sub_ne_zero.mpr (Ne.symm ho)];ring
    rw [cp,cp,show logTwo*(-s)=-logTwo*s by ring]
    simp only [thetaMultiplier,hZ]
    linear_combination (logTwo*(1-s)*dslope Complex.exp 0 (logTwo*(1-s))*completedRiemannZeta s)*he +
      ((Complex.exp (-logTwo*s)-1)*completedRiemannZeta s)*hf
  · have he := sub_smul_dslope Complex.exp 0 (-logTwo)
    have hExp : Complex.exp (-logTwo) = (1/2:ℂ) := by
      rw [Complex.exp_neg];unfold logTwo;rw [←Complex.ofReal_exp,Real.exp_log (by norm_num : (0:ℝ)<2)];norm_num
    simp only [sub_zero,smul_eq_mul,Complex.exp_zero,hExp] at he
    simp only [thetaMultiplier,mul_one,sub_self,mul_zero,dslope_same,Complex.deriv_exp,Complex.exp_zero,
      regZ,zero_mul,zero_sub,mul_neg,neg_mul,neg_neg]
    linear_combination -logTwo*he
