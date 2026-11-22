-- Prove2me | solution 1 for NLPrimitive.complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:20.787105+00:00
-- url     : https://prove2.me/submissions/c580aa73-ff77-4064-9963-e09509482e64

import Std
import Definitions.Def_NLPrimitive
import Theorems.Thm_NLPrimitive_canonical_truth

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution {Γ : Formula → Prop} {a : Formula}
    (h : Entails Γ a) : Derives Γ a := by
  have hΓ : ∀ b, Γ b →
      (canonical Γ).D (eval (canonical Γ).op Formula.var b) := by
    intro b hb
    exact (canonical_truth Γ b).mpr (Derives.hyp hb)
  exact (canonical_truth Γ a).mp (h Formula (canonical Γ) Formula.var hΓ)
end NLPrimitive
