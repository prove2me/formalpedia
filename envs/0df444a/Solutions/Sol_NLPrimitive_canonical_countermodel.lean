-- Prove2me | solution 1 for NLPrimitive.canonical_countermodel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:21.882216+00:00
-- url     : https://prove2.me/submissions/e9c65b4a-a4b7-4e90-ba7f-2328e2dd4e3f

import Std
import Definitions.Def_NLPrimitive
import Theorems.Thm_NLPrimitive_canonical_truth

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution {Γ : Formula → Prop} {a : Formula}
    (h : ¬ Derives Γ a) :
    (∀ b, Γ b → (canonical Γ).D (eval (canonical Γ).op Formula.var b)) ∧
    ¬ (canonical Γ).D (eval (canonical Γ).op Formula.var a) := by
  constructor
  · intro b hb
    exact (canonical_truth Γ b).mpr (Derives.hyp hb)
  · intro ha
    exact h ((canonical_truth Γ a).mp ha)
end NLPrimitive
