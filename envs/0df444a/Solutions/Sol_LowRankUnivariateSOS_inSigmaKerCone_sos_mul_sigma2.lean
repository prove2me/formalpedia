-- Prove2me | solution 1 for LowRankUnivariateSOS.inSigmaKerCone_sos_mul_sigma2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:27.366106+00:00
-- url     : https://prove2.me/submissions/e370ba0e-1bcd-4374-b0d7-1bffc788f8cb

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
import Theorems.Thm_LowRankUnivariateSOS_inKerA_perpPair_scalePair
import Theorems.Thm_LowRankUnivariateSOS_inSigmaKerCone_of_pair
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
theorem _root_.solution (g s : Poly) (u : UPair)
    (hs : IsSOS s) :
    InSigmaKerCone (scalePair g u) (s * sigma2 u) := by
  rcases hs with ⟨q₁, q₂, rfl⟩
  have hk₁ : InKerA (scalePair g u) (perpPair q₁ u) :=
    inKerA_perpPair_scalePair g q₁ u
  have hk₂ : InKerA (scalePair g u) (perpPair q₂ u) :=
    inKerA_perpPair_scalePair g q₂ u
  have hcone :
      InSigmaKerCone (scalePair g u)
        (sigma2 (perpPair q₁ u) + sigma2 (perpPair q₂ u)) :=
    inSigmaKerCone_of_pair hk₁ hk₂
  have hsigma :
      sigma2 (perpPair q₁ u) + sigma2 (perpPair q₂ u) = (q₁ ^ 2 + q₂ ^ 2) * sigma2 u := by
    simp [sigma2, pow_two]
    ring
  rw [hsigma] at hcone
  simpa using hcone
end LowRankUnivariateSOS
