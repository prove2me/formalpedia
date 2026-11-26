-- Prove2me | solution 1 for LowRankUnivariateSOS.dot_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:49.897312+00:00
-- url     : https://prove2.me/submissions/b787cb36-3dcb-4572-ad72-6f969b6ec9a8

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp
import Theorems.Thm_LowRankUnivariateSOS_dot_add_left
attribute [local simp] LowRankUnivariateSOS.dot_add_left

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}
namespace LowRankUnivariateSOS
theorem _root_.solution (p q r : Poly) :
    B p (q + r) = B p q + B p r := by
  simp
end LowRankUnivariateSOS
