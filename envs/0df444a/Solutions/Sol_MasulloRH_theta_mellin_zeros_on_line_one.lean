-- Prove2me | solution 1 for MasulloRH.theta_mellin_zeros_on_line_one
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:28:10.096775+00:00
-- url     : https://prove2.me/submissions/ec49b55c-c290-40a2-9628-212280e35ec7

import Theorems.Thm_MasulloRH_entire_theta_mellin_multiplier
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.Linarith

open MasulloRH.RationalThetaGrid

theorem solution (t : ℝ) : thetaMultiplier (point t) = 0 ↔ t ≠ 0 ∧ phase t = 1 := by
  have hL : logTwo ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  by_cases h : t = 0
  · subst t
    simp [point,vertical,MasulloRH.entire_theta_mellin_multiplier.2.2,hL]
  have hr : (point t).re = 1 := by simp [point,vertical]
  have hn : point t ≠ 0 := fun e => by rw [e] at hr;norm_num at hr
  have ho : point t ≠ 1 := fun e => h (by simpa [point,vertical] using congrArg Complex.im e)
  have hz : completedRiemannZeta (point t) ≠ 0 := by
    intro e
    have z := riemannZeta_ne_zero_of_one_le_re (s:=point t) hr.ge
    apply z
    rw [riemannZeta_def_of_ne_zero hn,e,zero_div]
  have cp (s : ℂ) : (2:ℂ)^s = Complex.exp (logTwo*s) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
    simp [logTwo,Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]
  have h2 : (2:ℂ)^(1-point t) = phase t := by rw [cp];unfold phase point;congr 1;ring
  have h1 : 1-(2:ℂ)^(-point t) ≠ 0 := by
    intro e
    have hg := congrArg norm ((sub_eq_zero.mp e).symm)
    rw [cp,Complex.norm_exp] at hg
    have re : (logTwo*(-point t)).re = -Real.log 2 := by
      simp only [logTwo,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,hr,
        mul_neg,mul_one,zero_mul,sub_zero]
    rw [re,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2),norm_one] at hg
    norm_num at hg
  rw [MasulloRH.entire_theta_mellin_multiplier.2.1 _ hn ho,h2]
  simp only [mul_eq_zero,h1,hz,false_or,or_false,sub_eq_zero]
  exact ⟨fun e => ⟨h,e.symm⟩,fun e => e.2.symm⟩
