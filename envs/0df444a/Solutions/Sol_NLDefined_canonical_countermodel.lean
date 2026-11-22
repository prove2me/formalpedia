-- Prove2me | solution 1 for NLDefined.canonical_countermodel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:17.547379+00:00
-- url     : https://prove2.me/submissions/ecca88fb-89d8-4cf3-a9d6-bfbd8f0cb95b

import Std
import Definitions.Def_NLDefined
import Theorems.Thm_NLDefined_canonical_truth

set_option autoImplicit true
set_option autoImplicit false
open NLDefined
namespace NLDefined
theorem _root_.solution {Γ : Formula → Prop} {a : Formula}
    (h : ¬ Derives Γ a) :
    (∀ b, Γ b → (canonical Γ).D (eval (canonical Γ).op Formula.var b)) ∧
    ¬ (canonical Γ).D (eval (canonical Γ).op Formula.var a) := by
  constructor
  · intro b hb
    exact (canonical_truth Γ b).mpr (Derives.hyp hb)
  · intro ha
    exact h ((canonical_truth Γ a).mp ha)
end NLDefined
