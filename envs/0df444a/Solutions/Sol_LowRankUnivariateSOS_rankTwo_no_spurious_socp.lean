-- Prove2me | solution 1 for LowRankUnivariateSOS.rankTwo_no_spurious_socp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:17.37911+00:00
-- url     : https://prove2.me/submissions/241949d8-0c64-4289-9b92-016efb565d05

import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebra
import Definitions.Def_LowRankUnivariateSOS_UnivariateSOS
import Definitions.Def_LowRankUnivariateSOS_RankTwoMain
import Theorems.Thm_LowRankUnivariateSOS_rankTwo_factored_h1_setup
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_self_eq_sigma2
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_A_zero_left
import Theorems.Thm_LowRankUnivariateSOS_A_zero_right
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
import Theorems.Thm_LowRankUnivariateSOS_factored_h1_residual_eq_zero
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_zero
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_sigma2_zero
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
import Theorems.Thm_LowRankUnivariateSOS_zero_fst
import Theorems.Thm_LowRankUnivariateSOS_zero_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_self_eq_sigma2
attribute [local simp] LowRankUnivariateSOS.A_smul_right
attribute [local simp] LowRankUnivariateSOS.A_zero_left
attribute [local simp] LowRankUnivariateSOS.A_zero_right
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_neg_left
attribute [local simp] LowRankUnivariateSOS.dot_neg_right
attribute [local simp] LowRankUnivariateSOS.dot_smul_left
attribute [local simp] LowRankUnivariateSOS.dot_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_zero_left
attribute [local simp] LowRankUnivariateSOS.dot_zero_right
attribute [local simp] LowRankUnivariateSOS.perpPair_fst
attribute [local simp] LowRankUnivariateSOS.perpPair_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_fst
attribute [local simp] LowRankUnivariateSOS.scalePair_snd
attribute [local simp] LowRankUnivariateSOS.scalePair_zero
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.sigma2_zero
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd
attribute [local simp] LowRankUnivariateSOS.zero_fst
attribute [local simp] LowRankUnivariateSOS.zero_snd



set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm} [Fact B.toQuadraticMap.PosDef]
namespace LowRankUnivariateSOS
theorem _root_.solution
    (p : Poly) (u : UPair)
    (hp : IsSOS p) (hsocp : IsSOCP B p u) :
    sigma2 u = p := by
  rcases rankTwo_factored_h1_setup (B := B) p u hp hsocp with
    ⟨a, g, q, s, u0, hu, hg, hcop, hs, hpq, himg⟩
  have hsocp' : IsSOCP B p (scalePair a u0) := by
    simpa [hu] using hsocp
  have hres : residual p u = 0 := by
    simpa [hu] using
      factored_h1_residual_eq_zero (B := B) a g p q s u0 hg hcop hs hpq himg hsocp'
  exact sub_eq_zero.mp (by simpa [residual] using hres)
end LowRankUnivariateSOS
