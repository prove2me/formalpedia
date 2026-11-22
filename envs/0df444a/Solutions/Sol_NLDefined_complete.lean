-- Prove2me | solution 1 for NLDefined.complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:16.959149+00:00
-- url     : https://prove2.me/submissions/a32fd09d-17b6-4940-a01a-d08f39ac6ae1

import Std
import Definitions.Def_NLDefined
import Theorems.Thm_NLDefined_canonical_truth

set_option autoImplicit true
set_option autoImplicit false
open NLDefined
namespace NLDefined
theorem _root_.solution {Γ : Formula → Prop} {a : Formula}
    (h : Entails Γ a) : Derives Γ a := by
  have hΓ : ∀ b, Γ b →
      (canonical Γ).D (eval (canonical Γ).op Formula.var b) := by
    intro b hb
    exact (canonical_truth Γ b).mpr (Derives.hyp hb)
  exact (canonical_truth Γ a).mp (h Formula (canonical Γ) Formula.var hΓ)
end NLDefined
