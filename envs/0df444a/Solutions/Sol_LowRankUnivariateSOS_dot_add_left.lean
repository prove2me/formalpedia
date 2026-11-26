-- Prove2me | solution 1 for LowRankUnivariateSOS.dot_add_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:16.056813+00:00
-- url     : https://prove2.me/submissions/c3102001-a5be-4d31-9737-78026cdad494

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Definitions.Def_LowRankUnivariateSOS_PolynomialModel
import Definitions.Def_LowRankUnivariateSOS_Socp

set_option autoImplicit true
noncomputable section
open LowRankUnivariateSOS
variable {B : DotForm}
namespace LowRankUnivariateSOS
theorem _root_.solution (p q r : Poly) :
    B (p + q) r = B p r + B q r := by
  simp
end LowRankUnivariateSOS
