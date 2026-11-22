-- Prove2me | solution 1 for NLPrimitive.canonical_truth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:54.04382+00:00
-- url     : https://prove2.me/submissions/c0cdae0a-bb0c-4d11-92da-6eca0c77d6d7

import Std
import Definitions.Def_NLPrimitive
import Theorems.Thm_NLPrimitive_eval_formulaOps

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution (Γ : Formula → Prop) (a : Formula) :
    (canonical Γ).D (eval (canonical Γ).op Formula.var a) ↔ Derives Γ a := by
  change Derives Γ (eval formulaOps Formula.var a) ↔ Derives Γ a
  rw [eval_formulaOps]
end NLPrimitive
