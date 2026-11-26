-- Prove2me | solution 1 for LowRankUnivariateSOS.A_self_eq_sigma2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:54.348931+00:00
-- url     : https://prove2.me/submissions/5d1660eb-c9ee-439b-ab8e-54aaeb6cd0df

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_right
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_left
import Theorems.Thm_LowRankUnivariateSOS_dot_neg_right
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_smul_left
attribute [local simp] LowRankUnivariateSOS.dot_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_zero_left
attribute [local simp] LowRankUnivariateSOS.dot_zero_right
attribute [local simp] LowRankUnivariateSOS.dot_neg_left
attribute [local simp] LowRankUnivariateSOS.dot_neg_right

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
namespace LowRankUnivariateSOS
theorem _root_.solution (u : UPair) : A u u = sigma2 u := by
  simp [A, sigma2, pow_two]
end LowRankUnivariateSOS
