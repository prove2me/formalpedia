-- Prove2me | solution 1 for LowRankUnivariateSOS.dot_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:55:27.68614+00:00
-- url     : https://prove2.me/submissions/ae780229-c87e-46f7-8c5a-281c14cc82b4

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_smul_left
attribute [local simp] LowRankUnivariateSOS.dot_smul_right

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}
namespace LowRankUnivariateSOS
theorem _root_.solution (p : Poly) : B 0 p = 0 := by
  simp
end LowRankUnivariateSOS
