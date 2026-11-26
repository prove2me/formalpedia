-- Prove2me | solution 1 for LowRankUnivariateSOS.inImageA_mul_of_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:37.825006+00:00
-- url     : https://prove2.me/submissions/d97dabae-e4c8-45f1-902c-37b14ddf4b3a

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
import Theorems.Thm_LowRankUnivariateSOS_inImageA_of_isCoprime
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
theorem _root_.solution (g q : Poly) (u : UPair)
    (hu : IsCoprime u.fst u.snd) :
    InImageA (scalePair g u) (g * q) := by
  rcases inImageA_of_isCoprime u hu q with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  simp [A_scalePair_left, hv]
end LowRankUnivariateSOS
