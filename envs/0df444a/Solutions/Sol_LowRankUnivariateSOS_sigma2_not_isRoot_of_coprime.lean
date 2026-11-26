-- Prove2me | solution 1 for LowRankUnivariateSOS.sigma2_not_isRoot_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:43.111697+00:00
-- url     : https://prove2.me/submissions/d319e089-a2b1-4b7f-bb2b-a5aa7dc5b796

import Definitions.Def_LowRankUnivariateSOS_H1Case
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain
import Definitions.Def_LowRankUnivariateSOS_UnivariateAlgebraCore
import Theorems.Thm_LowRankUnivariateSOS_A_scalePair_left
import Theorems.Thm_LowRankUnivariateSOS_A_smul_right
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
attribute [local simp] LowRankUnivariateSOS.A_smul_right
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
theorem _root_.solution
    (u : UPair) (hu : IsCoprime u.fst u.snd) (x : ℝ) :
    ¬ Polynomial.IsRoot (sigma2 u) x := by
  intro hsigma
  have hsum : u.fst.eval x ^ 2 + u.snd.eval x ^ 2 = 0 := by
    simpa [Polynomial.IsRoot, sigma2] using hsigma
  have hsquares : u.fst.eval x ^ 2 = 0 ∧ u.snd.eval x ^ 2 = 0 :=
    (add_eq_zero_iff_of_nonneg (sq_nonneg (u.fst.eval x)) (sq_nonneg (u.snd.eval x))).mp hsum
  have hroot_fst : Polynomial.IsRoot u.fst x := by
    simpa [Polynomial.IsRoot] using (sq_eq_zero_iff.mp hsquares.1)
  have hroot_snd : Polynomial.IsRoot u.snd x := by
    simpa [Polynomial.IsRoot] using (sq_eq_zero_iff.mp hsquares.2)
  have hdiv_fst : Polynomial.X - Polynomial.C x ∣ u.fst :=
    Polynomial.dvd_iff_isRoot.mpr hroot_fst
  have hdiv_snd : Polynomial.X - Polynomial.C x ∣ u.snd :=
    Polynomial.dvd_iff_isRoot.mpr hroot_snd
  have hunit : IsUnit (Polynomial.X - Polynomial.C x) :=
    hu.isUnit_of_dvd' hdiv_fst hdiv_snd
  exact Polynomial.not_isUnit_X_sub_C x hunit
end LowRankUnivariateSOS
