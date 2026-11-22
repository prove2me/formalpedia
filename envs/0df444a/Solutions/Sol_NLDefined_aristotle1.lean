-- Prove2me | solution 1 for NLDefined.aristotle1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:40.171798+00:00
-- url     : https://prove2.me/submissions/803b8a9a-b308-4542-aa5f-5fa9b41a3979

import Std
import Definitions.Def_NLDefined

set_option autoImplicit true
set_option autoImplicit false
open NLDefined
namespace NLDefined
theorem _root_.solution (a : Formula) :
    Theorem (Formula.neg (formulaOps.arr a (Formula.neg a))) := by
  have h1 : Theorem (formulaOps.arr a (Formula.neg (Formula.neg a))) :=
    Derives.ax (Axiom.a3 a)
  have h2 : Theorem (Formula.compat a (Formula.neg (Formula.neg a))) :=
    Derives.mp h1 (Derives.ax (Axiom.a4 a (Formula.neg (Formula.neg a))))
  exact Derives.mp h2
    (Derives.ax (Axiom.a3 (Formula.compat a (Formula.neg (Formula.neg a)))))
end NLDefined
