-- Prove2me | solution 1 for LowRankUnivariateSOS.dot_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:54:15.502717+00:00
-- url     : https://prove2.me/submissions/e06ab305-2520-4a66-964b-0d2b51c4ac9d

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
import Theorems.Thm_LowRankUnivariateSOS_dot_add_right
attribute [local simp] LowRankUnivariateSOS.dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_right

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}
namespace LowRankUnivariateSOS
theorem _root_.solution (a : ℝ) (p q : Poly) :
    B (a • p) q = a * B p q := by
  simp [smul_eq_mul]
end LowRankUnivariateSOS
