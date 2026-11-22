-- Prove2me | solution 1 for NLDefined.aristotle2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:43.222022+00:00
-- url     : https://prove2.me/submissions/158757d3-ef1f-4c58-b2bf-aa2de18fccc3

import Std
import Definitions.Def_NLDefined

set_option autoImplicit true
set_option autoImplicit false
open NLDefined
namespace NLDefined
theorem _root_.solution (a : Formula) :
    Theorem (Formula.neg (formulaOps.arr (Formula.neg a) a)) := by
  have h1 : Theorem (formulaOps.arr (Formula.neg a) (Formula.neg a)) :=
    Derives.ax (Axiom.a1 (Formula.neg a))
  have h2 : Theorem (Formula.compat (Formula.neg a) (Formula.neg a)) :=
    Derives.mp h1 (Derives.ax (Axiom.a4 (Formula.neg a) (Formula.neg a)))
  exact Derives.mp h2
    (Derives.ax (Axiom.a3 (Formula.compat (Formula.neg a) (Formula.neg a))))
end NLDefined
