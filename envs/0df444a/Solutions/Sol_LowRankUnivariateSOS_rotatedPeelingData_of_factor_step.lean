-- Prove2me | solution 1 for LowRankUnivariateSOS.rotatedPeelingData_of_factor_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:01:01.460514+00:00
-- url     : https://prove2.me/submissions/1685bbec-85a5-4e4a-9c58-81831d06628b

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
import Theorems.Thm_LowRankUnivariateSOS_inImageA_mul_of_isCoprime
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



set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution {u u0 : UPair} {a gStart gNext : Poly}
    (hu : u = scalePair a u0)
    (hcop : IsCoprime u0.fst u0.snd)
    (hfg : QuadraticFactorStep u0 gStart gNext)
    (q : Poly) (hq : InImageA (scalePair gNext u0) q) :
    Nonempty (RotatedPeelingData u (scalePair gStart u0) q) := by
  rcases hq with ⟨b, hb⟩
  rcases hfg.r_dvd_sigma with ⟨s, hs⟩
  refine ⟨
    { quad := perpPair 1 (scalePair gNext u0)
      const := perpPair 1 b
      quad_orth := ?_
      quad_in_prev_image := ?_
      cross_eq := ?_ }⟩
  · rw [InKerA, hu]
    simp [A, perpPair, scalePair]
    ring
  · have hquad :
      sigma2 (perpPair 1 (scalePair gNext u0)) =
        gStart * ((Polynomial.X ^ 2) * gNext * s) := by
      calc
        sigma2 (perpPair 1 (scalePair gNext u0)) = sigma2 (scalePair gNext u0) := by simp
        _ = gNext ^ 2 * sigma2 u0 := by simp
        _ = gNext ^ 2 * (hfg.r * s) := by rw [hs]
        _ = (gNext * hfg.r) * (gNext * s) := by ring
        _ = (Polynomial.X ^ 2 * gStart) * (gNext * s) := by rw [hfg.peel_eq]
        _ = gStart * ((Polynomial.X ^ 2) * gNext * s) := by ring
    have himg :
        InImageA (scalePair gStart u0) (gStart * ((Polynomial.X ^ 2) * gNext * s)) :=
      inImageA_mul_of_isCoprime gStart ((Polynomial.X ^ 2) * gNext * s) u0 hcop
    exact hquad ▸ himg
  · calc
      A (perpPair 1 (scalePair gNext u0)) (perpPair 1 b) = A (scalePair gNext u0) b := by
        simp [A_perpPair_right]
      _ = q := hb
end LowRankUnivariateSOS
