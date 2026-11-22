-- Prove2me | solution 1 for NLDefined.eval_formulaOps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:18.952971+00:00
-- url     : https://prove2.me/submissions/f8947917-564e-4c19-af30-ba3a4381a75c

import Std
import Definitions.Def_NLDefined

set_option autoImplicit true
set_option autoImplicit false
open NLDefined
namespace NLDefined
theorem _root_.solution (a : Formula) :
    eval formulaOps Formula.var a = a := by
  induction a <;> simp_all [eval, formulaOps]
end NLDefined
