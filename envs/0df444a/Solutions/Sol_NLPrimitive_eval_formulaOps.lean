-- Prove2me | solution 1 for NLPrimitive.eval_formulaOps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:26.605812+00:00
-- url     : https://prove2.me/submissions/3a54bcd6-ea83-41d7-98e3-ebd49b5581fd

import Std
import Definitions.Def_NLPrimitive

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution (a : Formula) :
    eval formulaOps Formula.var a = a := by
  induction a <;> simp_all [eval, formulaOps]
end NLPrimitive
