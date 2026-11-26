-- Prove2me | solution 1 for LowRankUnivariateSOS.inSigmaKerCone_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:51.030534+00:00
-- url     : https://prove2.me/submissions/896bd796-41bc-4f51-963b-a792ea71f292

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_Certificate
import Definitions.Def_LowRankUnivariateSOS_H1Case
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_inKerA_smul
attribute [local simp] LowRankUnivariateSOS.scalePair_fst
attribute [local simp] LowRankUnivariateSOS.scalePair_snd
attribute [local simp] LowRankUnivariateSOS.perpPair_fst
attribute [local simp] LowRankUnivariateSOS.perpPair_snd
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_smul_right
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution {u w₁ w₂ : UPair}
    (hw₁ : InKerA u w₁) (hw₂ : InKerA u w₂) :
    InSigmaKerCone u (sigma2 w₁ + sigma2 w₂) := by
  by_cases h : w₁ = w₂
  · refine ⟨{(Real.sqrt 2 : ℝ) • w₁}, ?_, ?_⟩
    · intro w hw
      have hw' : w = (Real.sqrt 2 : ℝ) • w₁ := by
        simpa using hw
      rcases hw' with rfl
      exact inKerA_smul (Real.sqrt 2) hw₁
    · subst h
      have hsqrt : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      simp [sigma2_smul, hsqrt, two_smul]
  · refine ⟨{w₁, w₂}, ?_, ?_⟩
    · intro w hw
      have hw' : w = w₁ ∨ w = w₂ := by
        simpa using hw
      rcases hw' with rfl | rfl
      · exact hw₁
      · exact hw₂
    · simp [h]
end LowRankUnivariateSOS
