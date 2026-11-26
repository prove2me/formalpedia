-- Prove2me | solution 1 for LowRankUnivariateSOS.dot_eq_zero_of_peeling_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:54.087115+00:00
-- url     : https://prove2.me/submissions/cfa286a7-be97-4143-adac-77cd9b4b7a7c

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_LowRankUnivariateSOS_FactoredCase
import Definitions.Def_LowRankUnivariateSOS_PeelingStep
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_self_eq_sigma2
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
import Theorems.Thm_LowRankUnivariateSOS_perpPair_fst
import Theorems.Thm_LowRankUnivariateSOS_perpPair_snd
import Theorems.Thm_LowRankUnivariateSOS_scalePair_fst
import Theorems.Thm_LowRankUnivariateSOS_scalePair_snd
import Theorems.Thm_LowRankUnivariateSOS_sigma2_perpPair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_scalePair
import Theorems.Thm_LowRankUnivariateSOS_sigma2_smul
import Theorems.Thm_LowRankUnivariateSOS_smul_fst
import Theorems.Thm_LowRankUnivariateSOS_smul_snd
attribute [local simp] LowRankUnivariateSOS.A_scalePair_left
attribute [local simp] LowRankUnivariateSOS.A_self_eq_sigma2
attribute [local simp] LowRankUnivariateSOS.A_smul_right
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
attribute [local simp] LowRankUnivariateSOS.sigma2_perpPair
attribute [local simp] LowRankUnivariateSOS.sigma2_scalePair
attribute [local simp] LowRankUnivariateSOS.sigma2_smul
attribute [local simp] LowRankUnivariateSOS.smul_fst
attribute [local simp] LowRankUnivariateSOS.smul_snd


section
noncomputable section
namespace LowRankUnivariateSOS
private theorem linear_nonneg_all_eq_zero {a c : ℝ}
    (h : ∀ η : ℝ, 0 ≤ (2 * η) * a + c) : a = 0 := by
  by_contra ha
  have htwo : (2 : ℝ) * a ≠ 0 := mul_ne_zero two_ne_zero ha
  have hbad : 0 ≤ (2 * (-(c + 1) / (2 * a))) * a + c :=
    h (-(c + 1) / (2 * a))
  have hvalue : (2 * (-(c + 1) / (2 * a))) * a + c = -1 := by
    field_simp [htwo]
    ring
  linarith
section DotForm
variable {B : DotForm}
end DotForm
section DotForm
variable {B : DotForm}
end DotForm
section DotForm
variable {B : DotForm}
end DotForm
end LowRankUnivariateSOS
end
end

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}
namespace LowRankUnivariateSOS
theorem _root_.solution {p : Poly} {u uImgPrev : UPair} {q : Poly}
    (hsocp : IsSOCP B p u)
    (hprev : ImageOrthogonalResidual B p u uImgPrev)
    (hstep : PeelingStepWitness u uImgPrev q) :
    B q (residual p u) = 0 := by
  let r := residual p u
  have hquad : B hstep.qQuad r = 0 :=
    hprev _ hstep.quad_in_prev_image
  have hη :
      ∀ η : ℝ,
        0 ≤ (2 * η) * B q r +
          (B hstep.sigmaConst r + 2 * B hstep.aConst hstep.aConst) := by
    intro η
    have hh : 0 ≤ hessianTerm B p u (hstep.family η) := hsocp.2 _
    rw [hessianTerm, hstep.A_const η, hstep.sigma_eq η] at hh
    simpa [r, add_assoc, add_left_comm, add_comm, hquad] using hh
  have hzero := linear_nonneg_all_eq_zero hη
  simpa [r] using hzero
end LowRankUnivariateSOS
