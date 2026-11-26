-- Prove2me | solution 1 for LowRankUnivariateSOS.dot_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:56:01.528182+00:00
-- url     : https://prove2.me/submissions/2658d3ab-fcb0-4a2e-b598-bac8cab23b49

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_left
import Theorems.Thm_LowRankUnivariateSOS_dot_smul_right
import Theorems.Thm_LowRankUnivariateSOS_dot_zero_left
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_smul_left
attribute [local simp] LowRankUnivariateSOS.dot_smul_right
attribute [local simp] LowRankUnivariateSOS.dot_zero_left

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}
namespace LowRankUnivariateSOS
theorem _root_.solution (p : Poly) : B p 0 = 0 := by
  simp
end LowRankUnivariateSOS
